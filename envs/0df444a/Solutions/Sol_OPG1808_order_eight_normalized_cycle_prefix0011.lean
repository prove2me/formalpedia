-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix0011
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:05:49.018263+00:00
-- url     : https://prove2.me/submissions/8a8137fe-1ff2-49eb-8012-048147fd1628

import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega
import Theorems.Thm_OPG1808_order_seven
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Order.PiLex

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cut8Prefix0011CompactV3Packet

section





namespace ModuleOPG1808CNF

variable {n : ℕ}

/-- Zero-based color-major arc index; DIMACS uses this index plus one. -/
def arcCode (c : Fin 3) (u v : Fin n) : ℕ := c.val * n * n + u.val * n + v.val

/-- The reachability atoms occupy the second block of `3*n*n` variables. -/
def reachCode (c : Fin 3) (u v : Fin n) : ℕ := 3 * n * n + arcCode c u v

abbrev Atom (n : ℕ) := ((Fin 2 × Fin 3) × Fin n) × Fin n

def pairIndex (n : ℕ) : (Fin 2 × Fin 3) × Fin n ≃ Fin ((2 * 3) * n) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def atomIndex (n : ℕ) : Atom n ≃ Fin (((2 * 3) * n) * n) :=
  ((pairIndex n).prodCongr (Equiv.refl _)).trans finProdFinEquiv

def atomCode (a : Atom n) : ℕ := (atomIndex n a).val

def arcAtom (c : Fin 3) (u v : Fin n) : Atom n := (((0, c), u), v)
def reachAtom (c : Fin 3) (u v : Fin n) : Atom n := (((1, c), u), v)

theorem atomCode_injective : Function.Injective (@atomCode n) := by
  intro a b h
  exact (atomIndex n).injective (Fin.ext h)

theorem arcAtom_code (c : Fin 3) (u v : Fin n) :
    atomCode (arcAtom c u v) = arcCode c u v := by
  simp [atomCode, atomIndex, pairIndex, arcAtom, arcCode, finProdFinEquiv,
    Nat.mul_add, Nat.mul_comm, Nat.add_comm]

theorem reachAtom_code (c : Fin 3) (u v : Fin n) :
    atomCode (reachAtom c u v) = reachCode c u v := by
  simp [atomCode, atomIndex, pairIndex, reachAtom, reachCode, arcCode, finProdFinEquiv,
    Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

/-- The six CNF concepts, with exactly-one split into three convenient fields.
This is a proof-local finite Boolean model, not a mathematical hypothesis added
onto the source theorem. `physical_model` constructs it from actual paths. -/
structure Model (word : Fin n → Fin 3) (val : Sat.Valuation) : Prop where
  orientation : ∀ (u v : Fin n), u ≠ v →
    val (arcCode 0 u v) ∨ val (arcCode 0 v u) ∨
      val (arcCode 1 u v) ∨ val (arcCode 1 v u) ∨
        val (arcCode 2 u v) ∨ val (arcCode 2 v u)
  color_exclusive : ∀ (c d : Fin 3) (u v : Fin n), c ≠ d →
    ¬ (val (arcCode c u v) ∧ val (arcCode d u v))
  direction_exclusive : ∀ (c d : Fin 3) (u v : Fin n), u ≠ v →
    ¬ (val (arcCode c u v) ∧ val (arcCode d v u))
  arc_reach : ∀ (c : Fin 3) (u v : Fin n), val (arcCode c u v) → val (reachCode c u v)
  reach_trans : ∀ (c : Fin 3) (u v w : Fin n),
    val (reachCode c u v) → val (reachCode c v w) → val (reachCode c u w)
  predecessor_forbidden : ∀ (c : Fin 3) (i : Fin n),
    ¬ val (reachCode c (finRotate n i) i)
  cycle : ∀ i : Fin n, val (arcCode (word i) i (finRotate n i))
  rainbow_forbidden : ∀ (a b c : Fin 3) (u v w : Fin n),
    a ≠ b → b ≠ c → c ≠ a → u ≠ v → v ≠ w → w ≠ u →
      ¬ (val (arcCode a u v) ∧ val (arcCode b v w) ∧ val (arcCode c w u))

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  have h : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

end ModuleOPG1808CNF
end

section




namespace ModuleOPG1808CNF.Model

open Sat

variable {n : ℕ} {word : Fin n → Fin 3} {val : Valuation}

theorem orientation_clause (h : Model word val) (u v : Fin n) (huv : u ≠ v) :
    val.satisfies [.pos (arcCode 0 u v), .pos (arcCode 0 v u),
      .pos (arcCode 1 u v), .pos (arcCode 1 v u),
      .pos (arcCode 2 u v), .pos (arcCode 2 v u)] := by
  intro h0 h0r h1 h1r h2 h2r
  rcases h.orientation u v huv with ha | ha | ha | ha | ha | ha
  · exact h0 ha
  · exact h0r ha
  · exact h1 ha
  · exact h1r ha
  · exact h2 ha
  · exact h2r ha

theorem colors_clause (h : Model word val) (c d : Fin 3) (u v : Fin n) (hcd : c ≠ d) :
    val.satisfies [.neg (arcCode c u v), .neg (arcCode d u v)] := by
  intro ha hb
  exact h.color_exclusive c d u v hcd ⟨ha, hb⟩

theorem opposites_clause (h : Model word val) (c d : Fin 3) (u v : Fin n) (huv : u ≠ v) :
    val.satisfies [.neg (arcCode c u v), .neg (arcCode d v u)] := by
  intro ha hb
  exact h.direction_exclusive c d u v huv ⟨ha, hb⟩

theorem arc_reach_clause (h : Model word val) (c : Fin 3) (u v : Fin n) :
    val.satisfies [.neg (arcCode c u v), .pos (reachCode c u v)] := by
  intro ha hnr
  exact hnr (h.arc_reach c u v ha)

theorem trans_clause (h : Model word val) (c : Fin 3) (u v w : Fin n) :
    val.satisfies [.neg (reachCode c u v), .neg (reachCode c v w),
      .pos (reachCode c u w)] := by
  intro huv hvw hnuw
  exact hnuw (h.reach_trans c u v w huv hvw)

theorem predecessor_clause (h : Model word val) (c : Fin 3) (i : Fin n) :
    val.satisfies [.neg (reachCode c (finRotate n i) i)] := by
  intro hr
  exact h.predecessor_forbidden c i hr

theorem cycle_clause (h : Model word val) (i : Fin n) :
    val.satisfies [.pos (arcCode (word i) i (finRotate n i))] := by
  intro hn
  exact hn (h.cycle i)

theorem color_unit_clause (h : Model word val) (c : Fin 3) (i : Fin n) (hc : word i = c) :
    val.satisfies [.pos (arcCode c i (finRotate n i))] := by
  subst c
  exact cycle_clause h i

theorem cycle_options_clause (h : Model word val) (i : Fin n) :
    val.satisfies [.pos (arcCode 0 i (finRotate n i)),
      .pos (arcCode 1 i (finRotate n i)), .pos (arcCode 2 i (finRotate n i))] := by
  intro h0 h1 h2
  have hw := h.cycle i
  rcases fin3_cases (word i) with hc | hc | hc
  · apply h0
    simpa only [hc] using hw
  · apply h1
    simpa only [hc] using hw
  · apply h2
    simpa only [hc] using hw

theorem rainbow_clause (h : Model word val) (a b c : Fin 3) (u v w : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u) :
    val.satisfies [.neg (arcCode a u v), .neg (arcCode b v w),
      .neg (arcCode c w u)] := by
  intro ha hb hc
  exact h.rainbow_forbidden a b c u v w hab hbc hca huv hvw hwu ⟨ha, hb, hc⟩

end ModuleOPG1808CNF.Model
end

section




namespace ModuleOPG1808CNF

variable {n : ℕ} [NeZero n] [NeZero (n - 1)]

/-- Equality of the initial `k` letters with a rotated, palette-permuted word. -/
def PrefixEq (word : Fin n → Fin 3) (r : Fin n) (σ : Equiv.Perm (Fin 3)) (k : ℕ) : Prop :=
  ∀ j : Fin n, j.val < k → word j = σ (word (j + r))

/-- Lexicographic orbit minimality expressed at a possible first differing index.
The finite orbit-minimum theorem supplies this condition independently. -/
def PrefixMinimal (word : Fin n → Fin 3) : Prop :=
  ∀ (r : Fin n) (σ : Equiv.Perm (Fin 3)) (i : Fin n),
    (∀ j : Fin n, j < i → word j = σ (word (j + r))) →
      word i ≤ σ (word (i + r))

/-- Zero-based prefix-variable code: `q=0` records equality of the first letter. -/
def prefixCode (t : ℕ) (q : Fin (n - 1)) : ℕ := 6 * n * n + (q.val + (n - 1) * t)

/-- Extend an arbitrary base valuation by genuine prefix equalities.
The transform metadata are explicit functions, and may repeat transformations. -/
def extendedVal (word : Fin n → Fin 3) (rot : ℕ → Fin n)
    (perm : ℕ → Equiv.Perm (Fin 3)) (base : Sat.Valuation) : Sat.Valuation :=
  fun k ↦ if k < 6 * n * n then base k else
    PrefixEq word (rot ((k - 6 * n * n) / (n - 1)))
      (perm ((k - 6 * n * n) / (n - 1))) ((k - 6 * n * n) % (n - 1) + 1)

omit [NeZero n] [NeZero (n - 1)] in
theorem arcCode_lt (c : Fin 3) (u v : Fin n) : arcCode c u v < 6 * n * n := by
  rw [← arcAtom_code]
  exact (atomIndex n (arcAtom c u v)).isLt

omit [NeZero n] [NeZero (n - 1)] in
theorem reachCode_lt (c : Fin 3) (u v : Fin n) : reachCode c u v < 6 * n * n := by
  rw [← reachAtom_code]
  exact (atomIndex n (reachAtom c u v)).isLt

omit [NeZero n] [NeZero (n - 1)] in
@[simp] theorem extendedVal_arc (word : Fin n → Fin 3) (rot : ℕ → Fin n)
    (perm : ℕ → Equiv.Perm (Fin 3)) (base : Sat.Valuation)
    (c : Fin 3) (u v : Fin n) :
    extendedVal word rot perm base (arcCode c u v) ↔ base (arcCode c u v) := by
  simp only [extendedVal, if_pos (arcCode_lt c u v)]

omit [NeZero n] [NeZero (n - 1)] in
@[simp] theorem extendedVal_reach (word : Fin n → Fin 3) (rot : ℕ → Fin n)
    (perm : ℕ → Equiv.Perm (Fin 3)) (base : Sat.Valuation)
    (c : Fin 3) (u v : Fin n) :
    extendedVal word rot perm base (reachCode c u v) ↔ base (reachCode c u v) := by
  simp only [extendedVal, if_pos (reachCode_lt c u v)]

omit [NeZero n] in
@[simp] theorem extendedVal_prefix (word : Fin n → Fin 3) (rot : ℕ → Fin n)
    (perm : ℕ → Equiv.Perm (Fin 3)) (base : Sat.Valuation)
    (t : ℕ) (q : Fin (n - 1)) :
    extendedVal word rot perm base (prefixCode t q) ↔
      PrefixEq word (rot t) (perm t) (q.val + 1) := by
  have hbound : ¬ prefixCode t q < 6 * n * n := by
    dsimp [prefixCode]
    omega
  rw [extendedVal, if_neg hbound]
  have hmpos : 0 < n - 1 := Nat.pos_of_ne_zero (NeZero.ne (n - 1))
  simp only [prefixCode, Nat.add_sub_cancel_left,
    Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt q.isLt,
    Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.isLt]

omit [NeZero n] [NeZero (n - 1)] in
/-- The semantic prefix gates do not change any original model clause. -/
theorem Model.extended {word : Fin n → Fin 3} {base : Sat.Valuation}
    (h : Model word base) (rot : ℕ → Fin n) (perm : ℕ → Equiv.Perm (Fin 3)) :
    Model word (extendedVal word rot perm base) := by
  constructor
  · intro u v huv
    simpa only [extendedVal_arc] using h.orientation u v huv
  · intro c d u v hcd
    simpa only [extendedVal_arc] using h.color_exclusive c d u v hcd
  · intro c d u v huv
    simpa only [extendedVal_arc] using h.direction_exclusive c d u v huv
  · intro c u v
    simpa only [extendedVal_arc, extendedVal_reach] using h.arc_reach c u v
  · intro c u v w
    simpa only [extendedVal_reach] using h.reach_trans c u v w
  · intro c i
    simpa only [extendedVal_reach] using h.predecessor_forbidden c i
  · intro i
    simpa only [extendedVal_arc] using h.cycle i
  · intro a b c u v w hab hbc hca huv hvw hwu
    simpa only [extendedVal_arc] using h.rainbow_forbidden a b c u v w hab hbc hca huv hvw hwu

/-- The extra model information used by the lex-leader clauses. -/
structure LexModel (word : Fin n → Fin 3) (rot : ℕ → Fin n)
    (perm : ℕ → Equiv.Perm (Fin 3)) (val : Sat.Valuation) : Prop extends Model word val where
  prefix_eq : ∀ (t : ℕ) (q : Fin (n - 1)), val (prefixCode t q) ↔
    PrefixEq word (rot t) (perm t) (q.val + 1)
  minimal : PrefixMinimal word

omit [NeZero n] in
theorem extended_model {word : Fin n → Fin 3} {base : Sat.Valuation}
    (h : Model word base) (hmin : PrefixMinimal word)
    (rot : ℕ → Fin n) (perm : ℕ → Equiv.Perm (Fin 3)) :
    LexModel word rot perm (extendedVal word rot perm base) where
  toModel := h.extended rot perm
  prefix_eq := extendedVal_prefix word rot perm base
  minimal := hmin

omit [NeZero n] [NeZero (n - 1)] in
/-- A forward-cycle arc has exactly its prescribed word color. -/
theorem Model.cycle_color {word : Fin n → Fin 3} {val : Sat.Valuation}
    (h : Model word val) (c : Fin 3) (i : Fin n)
    (ha : val (arcCode c i (finRotate n i))) : word i = c := by
  by_contra hne
  exact h.color_exclusive (word i) c i (finRotate n i) hne ⟨h.cycle i, ha⟩

omit [NeZero n] [NeZero (n - 1)] in
theorem prefixEq_zero (word : Fin n → Fin 3) (r : Fin n) (σ : Equiv.Perm (Fin 3)) :
    PrefixEq word r σ 0 := by
  intro j hj
  omega

omit [NeZero n] [NeZero (n - 1)] in
theorem prefixEq_step {word : Fin n → Fin 3} {r : Fin n} {σ : Equiv.Perm (Fin 3)}
    (i : Fin n) (hp : PrefixEq word r σ i.val) (hi : word i = σ (word (i + r))) :
    PrefixEq word r σ (i.val + 1) := by
  intro j hj
  by_cases hlt : j.val < i.val
  · exact hp j hlt
  · have heq : j = i := Fin.ext (by omega)
    simpa only [heq] using hi

/-- The comparison coordinate for prefix gate `q`. -/
def prefixPosition (q : Fin (n - 1)) : Fin n := ⟨q.val + 1, by have := q.isLt; omega⟩

/-- The successor prefix gate when another comparison coordinate remains. -/
def nextPrefix (q : Fin (n - 1)) (hnext : q.val + 1 < n - 1) : Fin (n - 1) :=
  ⟨q.val + 1, hnext⟩

namespace LexModel

open Sat

variable {word : Fin n → Fin 3} {rot : ℕ → Fin n}
  {perm : ℕ → Equiv.Perm (Fin 3)} {val : Valuation}

omit [NeZero (n - 1)] in
theorem first_word_eq_zero (h : LexModel word rot perm val) : word 0 = 0 := by
  have hle := h.minimal 0 (Equiv.swap (word 0) 0) 0 (fun j hj ↦ by
    change j.val < (0 : Fin n).val at hj
    simp only [Fin.val_zero] at hj
    omega)
  have hzero : word 0 ≤ 0 := by
    simpa only [zero_add, Equiv.swap_apply_left] using hle
  apply le_antisymm hzero
  change 0 ≤ (word 0).val
  exact Nat.zero_le _

omit [NeZero (n - 1)] in
theorem first_color_clause (h : LexModel word rot perm val) :
    val.satisfies [.pos (arcCode 0 0 (finRotate n 0))] :=
  Model.color_unit_clause h.toModel 0 0 (first_word_eq_zero h)

omit [NeZero (n - 1)] in
theorem first_conflict_clause (h : LexModel word rot perm val) (t : ℕ) (c d : Fin 3)
    (hlt : perm t d < c) :
    val.satisfies [.neg (arcCode c 0 (finRotate n 0)),
      .neg (arcCode d (rot t) (finRotate n (rot t)))] := by
  intro hc hd
  have hci := h.toModel.cycle_color c 0 hc
  have hdj := h.toModel.cycle_color d (rot t) hd
  have hle := h.minimal (rot t) (perm t) 0 (fun j hj ↦ by
    change j.val < (0 : Fin n).val at hj
    simp only [Fin.val_zero] at hj
    omega)
  apply (not_lt_of_ge hle)
  simpa only [hci, zero_add, hdj] using hlt

omit [NeZero n] [NeZero (n - 1)] in
theorem conflict_clause (h : LexModel word rot perm val) (t : ℕ)
    (q : Fin (n - 1)) (c d : Fin 3) (hlt : perm t d < c) :
    val.satisfies [.neg (prefixCode t q),
      .neg (arcCode c (prefixPosition q) (finRotate n (prefixPosition q))),
      .neg (arcCode d (prefixPosition q + rot t)
        (finRotate n (prefixPosition q + rot t)))] := by
  intro hp hc hd
  have hp' := (h.prefix_eq t q).mp hp
  have hci := h.toModel.cycle_color c (prefixPosition q) hc
  have hdj := h.toModel.cycle_color d (prefixPosition q + rot t) hd
  have hle := h.minimal (rot t) (perm t) (prefixPosition q) (fun j hj ↦ hp' j hj)
  apply (not_lt_of_ge hle)
  simpa only [hci, hdj] using hlt

theorem first_advance_clause (h : LexModel word rot perm val) (t : ℕ) (c d : Fin 3)
    (heq : c = perm t d) :
    val.satisfies [.neg (arcCode c 0 (finRotate n 0)),
      .neg (arcCode d (rot t) (finRotate n (rot t))), .pos (prefixCode (n := n) t (0 : Fin (n - 1)))] := by
  intro hc hd hnp
  apply hnp
  apply (h.prefix_eq t (0 : Fin (n - 1))).mpr
  have hci := h.toModel.cycle_color c 0 hc
  have hdj := h.toModel.cycle_color d (rot t) hd
  apply prefixEq_step 0 (prefixEq_zero word (rot t) (perm t))
  simpa only [zero_add] using hci.trans (heq.trans (congrArg (perm t) hdj).symm)

omit [NeZero n] [NeZero (n - 1)] in
theorem advance_clause (h : LexModel word rot perm val) (t : ℕ)
    (q : Fin (n - 1)) (c d : Fin 3) (hnext : q.val + 1 < n - 1)
    (heq : c = perm t d) :
    val.satisfies [.neg (prefixCode t q),
      .neg (arcCode c (prefixPosition q) (finRotate n (prefixPosition q))),
      .neg (arcCode d (prefixPosition q + rot t)
        (finRotate n (prefixPosition q + rot t))), .pos (prefixCode t (nextPrefix q hnext))] := by
  intro hp hc hd hnp
  apply hnp
  apply (h.prefix_eq t (nextPrefix q hnext)).mpr
  have hci := h.toModel.cycle_color c (prefixPosition q) hc
  have hdj := h.toModel.cycle_color d (prefixPosition q + rot t) hd
  apply prefixEq_step (prefixPosition q) ((h.prefix_eq t q).mp hp)
  exact hci.trans (heq.trans (congrArg (perm t) hdj).symm)

end LexModel

end ModuleOPG1808CNF
end

section



namespace OPG1808Cuts

open Sat ModuleOPG1808CNF

variable {n : ℕ}

/-- The number of variables before confined-path selectors are appended. -/
def selectorBase (n : ℕ) : ℕ := 6 * n * n + (6 * n - 1) * (n - 1)

/-- Zero-based code; the native DIMACS selector is this number plus one. -/
def selectorCode (length : ℕ) (u : Fin n) (k : Fin 3) : ℕ :=
  selectorBase n + 3 * n * (length - 3) + 3 * u.val + k.val

/-- The `j`th vertex in the cyclic interval starting at `u`. -/
def cyclicVertex [NeZero n] (u : Fin n) (j : ℕ) : Fin n := u + Fin.ofNat n j

/-- A finite clause mentions only variables strictly below this boundary. -/
def clauseBelow (bound : ℕ) (c : List Literal) : Prop :=
  ∀ l ∈ c, match l with
    | .pos i => i < bound
    | .neg i => i < bound

instance (bound : ℕ) (c : List Literal) : Decidable (clauseBelow bound c) := by
  let p : Literal → Prop := fun l ↦ match l with
    | .pos i => i < bound
    | .neg i => i < bound
  letI : DecidablePred p := fun l ↦ by cases l <;> exact inferInstance
  exact List.decidableBAll p c

/-- Clause proofs depend only on the variables they mention. -/
theorem satisfies_of_below {base val : Valuation} {bound : ℕ} {c : List Literal}
    (heq : ∀ i, i < bound → (val i ↔ base i))
    (hc : clauseBelow bound c) (hs : base.satisfies c) : val.satisfies c := by
  induction c with
  | nil => exact hs
  | cons l c ih =>
    intro hl
    apply ih (fun l hl ↦ hc l (List.mem_cons_of_mem _ hl))
    apply hs
    have hi := hc l (List.mem_cons_self)
    cases l with
    | pos i => exact fun hb ↦ hl ((heq i hi).mpr hb)
    | neg i => exact (heq i hi).mp hl

/-- Emitter convenience: infer the clause from its proof before deciding support. -/
theorem satisfies_of_below' {base val : Valuation} {bound : ℕ} {c : List Literal}
    (heq : ∀ i, i < bound → (val i ↔ base i))
    (hs : base.satisfies c) (hc : clauseBelow bound c) : val.satisfies c :=
  satisfies_of_below heq hc hs

/-- A true positive literal suffices to satisfy the whole clause. -/
theorem satisfies_of_pos_mem {val : Valuation} {i : ℕ} {c : List Literal}
    (hi : val i) (hc : Literal.pos i ∈ c) : val.satisfies c := by
  induction c with
  | nil => exact False.elim (List.not_mem_nil hc)
  | cons l c ih =>
    intro hl
    rcases List.mem_cons.mp hc with heq | hmem
    · subst l
      exact False.elim (hl hi)
    · exact ih hmem

/-- Source is in the cut; target is out; interior membership is its mask bit. -/
def maskSide (length mask j : ℕ) : Bool :=
  j == 0 || (decide (j + 1 < length) && mask.testBit (j - 1))

def cutLeft (d mask : ℕ) : List (Fin (d + 3)) :=
  (List.finRange (d + 3)).filter (fun j ↦ maskSide (d + 3) mask j.val)

def cutRight (d mask : ℕ) : List (Fin (d + 3)) :=
  (List.finRange (d + 3)).filter (fun j ↦ !maskSide (d + 3) mask j.val)

/-- Exact ordered literal list: negative selector, then left-major crossing arcs. -/
noncomputable def cutClause [NeZero n] (d : ℕ) (u : Fin n) (k : Fin 3) (mask : ℕ) : List Literal :=
  .neg (selectorCode (d + 3) u k) ::
    (cutLeft d mask).flatMap (fun a ↦ (cutRight d mask).map (fun b ↦
      .pos (arcCode k (cyclicVertex u a.val) (cyclicVertex u b.val))))

/-- The additional finite Boolean information, supplied from actual confined
paths by `physical_cut_model`; no old `Model` or `LexModel` is changed. -/
structure CutModel [NeZero n] (bound : ℕ) (val : Valuation) : Prop where
  ambient_positive : ∀ (u : Fin n) (d : ℕ), 2 ≤ d → d + 1 ≤ bound →
    ∃ k : Fin 3, val (reachCode k u (cyclicVertex u d))
  selector_positive : ∀ (d : ℕ), d + 3 ≤ bound → ∀ u : Fin n,
    ∃ k : Fin 3, val (selectorCode (d + 3) u k)
  selector_reach : ∀ (d : ℕ), d + 3 ≤ bound → ∀ (u : Fin n) (k : Fin 3),
    val (selectorCode (d + 3) u k) →
      val (reachCode k u (cyclicVertex u (d + 2)))
  selector_cut : ∀ (d : ℕ), d + 3 ≤ bound → ∀ (u : Fin n) (k : Fin 3)
    (S : Fin (d + 3) → Prop), S 0 → ¬S (Fin.last (d + 2)) →
    val (selectorCode (d + 3) u k) →
      ∃ a b : Fin (d + 3), S a ∧ ¬S b ∧
        val (arcCode k (cyclicVertex u a.val) (cyclicVertex u b.val))

namespace CutModel

variable [NeZero n] {bound : ℕ} {val : Valuation}

theorem ambient_clause (h : CutModel (n := n) bound val) (u : Fin n) (d : ℕ)
    (hlo : 2 ≤ d) (hhi : d + 1 ≤ bound) :
    val.satisfies [.pos (reachCode 0 u (cyclicVertex u d)),
      .pos (reachCode 1 u (cyclicVertex u d)),
      .pos (reachCode 2 u (cyclicVertex u d))] := by
  intro h0 h1 h2
  obtain ⟨k, hk⟩ := h.ambient_positive u d hlo hhi
  rcases fin3_cases k with rfl | rfl | rfl
  · exact h0 hk
  · exact h1 hk
  · exact h2 hk

theorem selector_clause (h : CutModel (n := n) bound val) (d : ℕ)
    (hhi : d + 3 ≤ bound) (u : Fin n) :
    val.satisfies [.pos (selectorCode (d + 3) u 0),
      .pos (selectorCode (d + 3) u 1), .pos (selectorCode (d + 3) u 2)] := by
  intro h0 h1 h2
  obtain ⟨k, hk⟩ := h.selector_positive d hhi u
  rcases fin3_cases k with rfl | rfl | rfl
  · exact h0 hk
  · exact h1 hk
  · exact h2 hk

theorem reach_clause (h : CutModel (n := n) bound val) (d : ℕ)
    (hhi : d + 3 ≤ bound) (u : Fin n) (k : Fin 3) :
    val.satisfies [.neg (selectorCode (d + 3) u k),
      .pos (reachCode k u (cyclicVertex u (d + 2)))] := by
  intro hb hnr
  exact hnr (h.selector_reach d hhi u k hb)

theorem cut_clause (h : CutModel (n := n) bound val) (d : ℕ)
    (hhi : d + 3 ≤ bound) (u : Fin n) (k : Fin 3) (mask : ℕ) :
    val.satisfies (cutClause d u k mask) := by
  intro hb
  obtain ⟨a, b, ha, hb', hab⟩ := h.selector_cut d hhi u k
    (fun j ↦ maskSide (d + 3) mask j.val = true)
    (by simp only [Fin.val_zero, maskSide, beq_self_eq_true, Bool.true_or])
    (by simp only [Fin.val_last, maskSide]; simp)
    hb
  apply satisfies_of_pos_mem hab
  apply List.mem_flatMap.mpr
  refine ⟨a, ?_, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
  · exact List.mem_filter.mpr ⟨List.mem_finRange a, ha⟩
  · exact List.mem_filter.mpr ⟨List.mem_finRange b, by simpa using hb'⟩

end CutModel
end OPG1808Cuts
end

section

open Function

namespace OPG1808Audit

universe u

/-- Every map on a nonempty finite type has a positive-period point. -/
theorem exists_periodic_point {V : Type u} [Fintype V] [Nonempty V] (f : V → V) :
    ∃ a : V, ∃ p : ℕ, 0 < p ∧ IsPeriodicPt f p a := by
  classical
  let x : V := Classical.arbitrary V
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) ↦ f^[i.val] x) (by simp)
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨f^[i.val] x, j.val - i.val, Nat.sub_pos_of_lt hlt, ?_⟩
    change f^[j.val - i.val] (f^[i.val] x) = f^[i.val] x
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq.symm
  · refine ⟨f^[j.val] x, i.val - j.val, Nat.sub_pos_of_lt hlt, ?_⟩
    change f^[i.val - j.val] (f^[j.val] x) = f^[j.val] x
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq

/-- A finite relation with an incoming predecessor at every vertex has a simple directed cycle.
The indexing follows the chosen predecessor map, so relation arrows point backwards. -/
theorem exists_simple_cycle_of_predecessor {V : Type u} [Fintype V] [Nonempty V]
    (R : V → V → Prop) (hpred : ∀ v : V, ∃ w : V, R w v) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, R (e (finRotate m i)) (e i) := by
  classical
  let f : V → V := fun v ↦ Classical.choose (hpred v)
  have hf : ∀ v : V, R (f v) v := fun v ↦ Classical.choose_spec (hpred v)
  obtain ⟨a, p, hp, hperiod⟩ := exists_periodic_point f
  let m := minimalPeriod f a
  have hm : 0 < m := hperiod.minimalPeriod_pos hp
  have hcard : m ≤ Fintype.card V := minimalPeriod_le_card
  let e : Fin m → V := fun i ↦ f^[i.val] a
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij
  have hs : ∀ i : Fin m, e (finRotate m i) = f (e i) := by
    intro i
    have hrot : (finRotate m i).val = (i.val + 1) % m := by
      let inst : NeZero m := ⟨Nat.ne_of_gt hm⟩
      rw [finRotate_apply, Fin.val_add, Fin.val_one']
      simp only [Nat.add_mod, Nat.mod_mod]
    change f^[(finRotate m i).val] a = f (f^[i.val] a)
    rw [hrot, (isPeriodicPt_minimalPeriod f a).iterate_mod_apply, iterate_succ_apply']
  refine ⟨m, hm, hcard, e, he, ?_⟩
  intro i
  rw [hs]
  exact hf (e i)

/-- Reversing the indexing makes the arrows follow `finRotate`, as in a SAT cycle. -/
theorem exists_forward_simple_cycle_of_predecessor {V : Type u} [Fintype V] [Nonempty V]
    (R : V → V → Prop) (hpred : ∀ v : V, ∃ w : V, R w v) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, R (e i) (e (finRotate m i)) := by
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ := exists_simple_cycle_of_predecessor R hpred
  let inst : NeZero m := ⟨Nat.ne_of_gt hm⟩
  refine ⟨m, hm, hcard, (fun i ↦ e (-i)), he.comp neg_injective, ?_⟩
  intro i
  have hrev : finRotate m (-(finRotate m i)) = -i := by
    simp [finRotate_apply, add_assoc]
  simpa only [hrev] using hcycle (-(finRotate m i))

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808Audit

universe u v

/-- Monochromatic paths in an induced graph give paths in the original graph. -/
theorem monochromatically_reaches_map {V : Type u} {W : Type v}
    (D : Digraph V) (color : ArcColoring V) (e : W → V) {s t : W}
    (h : MonochromaticallyReaches (fun i j ↦ D (e i) (e j))
      (fun i j ↦ color (e i) (e j)) s t) :
    MonochromaticallyReaches D color (e s) (e t) := by
  obtain ⟨k, hpath⟩ := h
  exact ⟨k, hpath.lift e (fun _ _ h ↦ h)⟩

/-- Tournament structure restricts along an injective vertex map. -/
theorem is_tournament_map {V : Type u} {W : Type v}
    (D : Digraph V) (e : W → V) (he : Function.Injective e) (ht : IsTournament D) :
    IsTournament (fun i j ↦ D (e i) (e j)) := by
  constructor
  · intro i
    exact ht.1 (e i)
  · intro i j hij
    exact ht.2 (fun h ↦ hij (he h))

/-- A rainbow directed triangle in an induced graph is one in the original graph. -/
theorem no_rainbow_map {V : Type u} {W : Type v}
    (D : Digraph V) (color : ArcColoring V) (e : W → V) (he : Function.Injective e)
    (h : ¬HasRainbowDirectedTriangle D color) :
    ¬HasRainbowDirectedTriangle (fun i j ↦ D (e i) (e j))
      (fun i j ↦ color (e i) (e j)) := by
  rintro ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, hCab, hCbc, hCca⟩
  exact h ⟨e a, e b, e c, he.ne hab, he.ne hbc, he.ne hca,
    hDab, hDbc, hDca, hCab, hCbc, hCca⟩

/-- A no-source tournament contains an injectively labelled physical cycle whose
vertices cannot reach their cycle predecessors monochromatically. No minimality
or positive non-predecessor reachability assumption is needed. -/
theorem missing_predecessor_cycle_of_no_source
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hnosource : ¬∃ s : V, IsMonochromaticSource D color s) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ Fintype.card V ∧
      ∃ e : Fin m → V, Function.Injective e ∧
        ∀ i : Fin m, D (e i) (e (finRotate m i)) ∧
          ¬MonochromaticallyReaches D color (e (finRotate m i)) (e i) := by
  classical
  let R : V → V → Prop := fun u v ↦ ¬MonochromaticallyReaches D color v u
  have hpred : ∀ v : V, ∃ w : V, R w v := by
    intro v
    by_contra hmiss
    apply hnosource
    refine ⟨v, fun w ↦ ?_⟩
    by_contra hw
    exact hmiss ⟨w, hw⟩
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ := exists_forward_simple_cycle_of_predecessor R hpred
  have hne : ∀ i : Fin m, e i ≠ e (finRotate m i) := by
    intro i hEq
    apply hcycle i
    rw [← hEq]
    exact ⟨0, .refl⟩
  have harc : ∀ i : Fin m, D (e i) (e (finRotate m i)) := by
    intro i
    rcases (ht.2 (hne i)).1 with hforward | hbackward
    · exact hforward
    · exact False.elim (hcycle i ⟨color (e (finRotate m i)) (e i), .single ⟨hbackward, rfl⟩⟩)
  have hm1 : m ≠ 1 := by
    intro heq
    subst m
    exact hne 0 (congrArg e (Subsingleton.elim _ _))
  have hm2 : m ≠ 2 := by
    intro heq
    subst m
    have hrot0 : finRotate 2 (0 : Fin 2) = 1 := by decide
    have hrot1 : finRotate 2 (1 : Fin 2) = 0 := by decide
    have h01 : D (e 0) (e 1) := by simpa only [hrot0] using harc 0
    have h10 : D (e 1) (e 0) := by simpa only [hrot1] using harc 1
    exact (ht.2 (he.ne (by decide : (0 : Fin 2) ≠ 1))).2 ⟨h01, h10⟩
  refine ⟨m, by omega, hcard, e, he, ?_⟩
  intro i
  exact ⟨harc i, hcycle i⟩

end OPG1808Audit
end

section

open OPG1808

namespace OPG1808Intervals

universe u

/-- In a chain of at most seven distinct vertices, failure to reach the
preceding vertex rules out every source except the first vertex. -/
theorem first_reaches_chain
    {V : Type u} (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (d : ℕ) (hd : d ≤ 6) (e : Fin (d + 1) → V)
    (he : Function.Injective e)
    (hmissing : ∀ j : Fin d,
      ¬MonochromaticallyReaches D color (e j.succ) (e j.castSucc)) :
    ∀ j : Fin (d + 1), MonochromaticallyReaches D color (e 0) (e j) := by
  let D' : Digraph (Fin (d + 1)) := fun i j ↦ D (e i) (e j)
  let color' : ArcColoring (Fin (d + 1)) := fun i j ↦ color (e i) (e j)
  obtain ⟨s, hs⟩ := OPG1808.order_seven D' color'
    (OPG1808Audit.is_tournament_map D e he ht)
    (by simpa only [Fintype.card_fin] using (show d + 1 ≤ 7 by omega))
    (OPG1808Audit.no_rainbow_map D color e he hno)
  have honly : ∀ s : Fin (d + 1), IsMonochromaticSource D' color' s → s = 0 := by
    intro s
    refine Fin.cases (fun _ ↦ rfl) (fun j hj ↦ ?_) s
    exact False.elim (hmissing j
      (OPG1808Audit.monochromatically_reaches_map D color e (hj j.castSucc)))
  have hs0 := honly s hs
  subst s
  intro j
  exact OPG1808Audit.monochromatically_reaches_map D color e (hs j)

/-- A bad cycle has positive monochromatic reachability across every forward
interval containing at most seven vertices. This is a consequence of the
accepted bound through seven, rather than an additional cycle assumption. -/
theorem short_forward_reachable
    {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (D : Digraph (Fin m)) (color : ArcColoring (Fin m))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hmissing : ∀ j : Fin m,
      ¬MonochromaticallyReaches D color (finRotate m j) j)
    (i : Fin m) (d : ℕ) (hd : d ≤ 6) (hdm : d < m) :
    MonochromaticallyReaches D color i (i + ⟨d, hdm⟩) := by
  let hbound : d + 1 ≤ m := by omega
  let e : Fin (d + 1) → Fin m := fun j ↦ i + Fin.castLE hbound j
  have he : Function.Injective e := by
    intro a b hab
    have hc : Fin.castLE hbound a = Fin.castLE hbound b := add_left_cancel hab
    exact Fin.ext (congrArg (fun x : Fin m ↦ x.val) hc)
  have hs : ∀ j : Fin d, e j.succ = finRotate m (e j.castSucc) := by
    intro j
    change i + Fin.castLE hbound j.succ =
      finRotate m (i + Fin.castLE hbound j.castSucc)
    rw [finRotate_apply, add_assoc]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_castLE, Fin.val_succ, Fin.val_castSucc,
      Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < m),
      Nat.mod_eq_of_lt (by omega : j.val + 1 < m)]
  have hr := first_reaches_chain D color ht hno d hd e he (fun j ↦ by
    rw [hs j]
    exact hmissing (e j.castSucc)) ⟨d, by omega⟩
  have he0 : e 0 = i := by
    have hz : Fin.castLE hbound (0 : Fin (d + 1)) = (0 : Fin m) := by
      apply Fin.ext
      simp only [Fin.val_castLE, Fin.val_zero]
    change i + Fin.castLE hbound 0 = i
    rw [hz, add_zero]
  have helast : e ⟨d, by omega⟩ = i + ⟨d, hdm⟩ := by rfl
  simpa only [he0, helast] using hr


end OPG1808Intervals
end

section

open OPG1808

namespace OPG1808Intervals

universe u

/-- The source on a bounded chain is the first vertex, and its witnessing
paths stay inside that chain's induced tournament. -/
theorem first_is_source_on_chain
    {V : Type u} (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (d : ℕ) (hd : d ≤ 6) (e : Fin (d + 1) → V)
    (he : Function.Injective e)
    (hmissing : ∀ j : Fin d,
      ¬MonochromaticallyReaches D color (e j.succ) (e j.castSucc)) :
    IsMonochromaticSource (fun i j ↦ D (e i) (e j))
      (fun i j ↦ color (e i) (e j)) (0 : Fin (d + 1)) := by
  let D' : Digraph (Fin (d + 1)) := fun i j ↦ D (e i) (e j)
  let color' : ArcColoring (Fin (d + 1)) := fun i j ↦ color (e i) (e j)
  obtain ⟨s, hs⟩ := OPG1808.order_seven D' color'
    (OPG1808Audit.is_tournament_map D e he ht)
    (by simpa only [Fintype.card_fin] using (show d + 1 ≤ 7 by omega))
    (OPG1808Audit.no_rainbow_map D color e he hno)
  have honly : ∀ s : Fin (d + 1), IsMonochromaticSource D' color' s → s = 0 := by
    intro s
    refine Fin.cases (fun _ ↦ rfl) (fun j hj ↦ ?_) s
    exact False.elim (hmissing j
      (OPG1808Audit.monochromatically_reaches_map D color e (hj j.castSucc)))
  have hs0 := honly s hs
  subst s
  exact hs

/-- A path crossing a cut contains an arc leaving that cut. The endpoints of
the arc remain in the path's carrier, so induced paths yield confined cuts. -/
theorem colored_path_crosses_cut
    {V : Type u} (D : Digraph V) (color : ArcColoring V)
    (k : Fin 3) {s t : V}
    (hpath : Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k) s t)
    (S : V → Prop) (hs : S s) (ht : ¬S t) :
    ∃ a b : V, S a ∧ ¬S b ∧ D a b ∧ color a b = k := by
  classical
  by_contra hcross
  have hclosed : ∀ {a b : V}, S a → D a b ∧ color a b = k → S b := by
    intro a b ha hab
    by_contra hb
    exact hcross ⟨a, b, ha, hb, hab.1, hab.2⟩
  have hpreserve : ∀ {v : V},
      Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k) s v → S v := by
    intro v hp
    induction hp with
    | refl => exact hs
    | tail _ hab ih => exact hclosed ih hab
  exact ht (hpreserve hpath)


end OPG1808Intervals
end

section

open OPG1808

namespace OPG1808CNF

variable {n : ℕ}

/-- Zero-based color-major arc index; DIMACS uses this index plus one. -/
def arcCode (c : Fin 3) (u v : Fin n) : ℕ := c.val * n * n + u.val * n + v.val

/-- The reachability atoms occupy the second block of `3*n*n` variables. -/
def reachCode (c : Fin 3) (u v : Fin n) : ℕ := 3 * n * n + arcCode c u v

abbrev Atom (n : ℕ) := ((Fin 2 × Fin 3) × Fin n) × Fin n

def pairIndex (n : ℕ) : (Fin 2 × Fin 3) × Fin n ≃ Fin ((2 * 3) * n) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def atomIndex (n : ℕ) : Atom n ≃ Fin (((2 * 3) * n) * n) :=
  ((pairIndex n).prodCongr (Equiv.refl _)).trans finProdFinEquiv

def atomCode (a : Atom n) : ℕ := (atomIndex n a).val

def arcAtom (c : Fin 3) (u v : Fin n) : Atom n := (((0, c), u), v)
def reachAtom (c : Fin 3) (u v : Fin n) : Atom n := (((1, c), u), v)

theorem atomCode_injective : Function.Injective (@atomCode n) := by
  intro a b h
  exact (atomIndex n).injective (Fin.ext h)

theorem arcAtom_code (c : Fin 3) (u v : Fin n) :
    atomCode (arcAtom c u v) = arcCode c u v := by
  simp [atomCode, atomIndex, pairIndex, arcAtom, arcCode, finProdFinEquiv,
    Nat.mul_add, Nat.mul_comm, Nat.add_comm]

theorem reachAtom_code (c : Fin 3) (u v : Fin n) :
    atomCode (reachAtom c u v) = reachCode c u v := by
  simp [atomCode, atomIndex, pairIndex, reachAtom, reachCode, arcCode, finProdFinEquiv,
    Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

def atomProp (D : Digraph (Fin n)) (color : ArcColoring (Fin n)) (a : Atom n) : Prop :=
  if a.1.1.1 = 0 then D a.1.2 a.2 ∧ color a.1.2 a.2 = a.1.1.2
  else Relation.ReflTransGen (fun x y ↦ D x y ∧ color x y = a.1.1.2) a.1.2 a.2

/-- A total valuation; indices not coding typed atoms are false. -/
def physicalVal (D : Digraph (Fin n)) (color : ArcColoring (Fin n)) : Sat.Valuation :=
  fun k ↦ ∃ a : Atom n, atomCode a = k ∧ atomProp D color a

theorem physicalVal_code (D : Digraph (Fin n)) (color : ArcColoring (Fin n)) (a : Atom n) :
    physicalVal D color (atomCode a) ↔ atomProp D color a := by
  constructor
  · rintro ⟨b, heq, hb⟩
    exact atomCode_injective heq ▸ hb
  · exact fun ha ↦ ⟨a, rfl, ha⟩

@[simp] theorem physicalVal_arc (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (c : Fin 3) (u v : Fin n) :
    physicalVal D color (arcCode c u v) ↔ D u v ∧ color u v = c := by
  rw [← arcAtom_code, physicalVal_code]
  simp [atomProp, arcAtom]

@[simp] theorem physicalVal_reach (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (c : Fin 3) (u v : Fin n) :
    physicalVal D color (reachCode c u v) ↔
      Relation.ReflTransGen (fun x y ↦ D x y ∧ color x y = c) u v := by
  rw [← reachAtom_code, physicalVal_code]
  simp [atomProp, reachAtom]

/-- The six CNF concepts, with exactly-one split into three convenient fields.
This is a proof-local finite Boolean model, not a mathematical hypothesis added
onto the source theorem. `physical_model` constructs it from actual paths. -/
structure Model (word : Fin n → Fin 3) (val : Sat.Valuation) : Prop where
  orientation : ∀ (u v : Fin n), u ≠ v →
    val (arcCode 0 u v) ∨ val (arcCode 0 v u) ∨
      val (arcCode 1 u v) ∨ val (arcCode 1 v u) ∨
        val (arcCode 2 u v) ∨ val (arcCode 2 v u)
  color_exclusive : ∀ (c d : Fin 3) (u v : Fin n), c ≠ d →
    ¬ (val (arcCode c u v) ∧ val (arcCode d u v))
  direction_exclusive : ∀ (c d : Fin 3) (u v : Fin n), u ≠ v →
    ¬ (val (arcCode c u v) ∧ val (arcCode d v u))
  arc_reach : ∀ (c : Fin 3) (u v : Fin n), val (arcCode c u v) → val (reachCode c u v)
  reach_trans : ∀ (c : Fin 3) (u v w : Fin n),
    val (reachCode c u v) → val (reachCode c v w) → val (reachCode c u w)
  predecessor_forbidden : ∀ (c : Fin 3) (i : Fin n),
    ¬ val (reachCode c (finRotate n i) i)
  cycle : ∀ i : Fin n, val (arcCode (word i) i (finRotate n i))
  rainbow_forbidden : ∀ (a b c : Fin 3) (u v w : Fin n),
    a ≠ b → b ≠ c → c ≠ a → u ≠ v → v ≠ w → w ≠ u →
      ¬ (val (arcCode a u v) ∧ val (arcCode b v w) ∧ val (arcCode c w u))

theorem fin3_cases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
  have h : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem physical_model (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (word : Fin n → Fin 3) (ht : IsTournament D)
    (hno : ¬ HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin n, D i (finRotate n i) ∧ color i (finRotate n i) = word i)
    (hmiss : ∀ i : Fin n, ¬ MonochromaticallyReaches D color (finRotate n i) i) :
    Model word (physicalVal D color) := by
  constructor
  · intro u v huv
    simp only [physicalVal_arc]
    rcases (ht.2 huv).1 with hD | hD
    · rcases fin3_cases (color u v) with hc | hc | hc <;> simp [hD, hc]
    · rcases fin3_cases (color v u) with hc | hc | hc <;> simp [hD, hc]
  · intro c d u v hcd
    rintro ⟨hc, hd⟩
    exact hcd (((physicalVal_arc D color c u v).mp hc).2.symm.trans
      ((physicalVal_arc D color d u v).mp hd).2)
  · intro c d u v huv
    rintro ⟨hc, hd⟩
    exact (ht.2 huv).2 ⟨((physicalVal_arc D color c u v).mp hc).1,
      ((physicalVal_arc D color d v u).mp hd).1⟩
  · intro c u v ha
    exact (physicalVal_reach D color c u v).mpr
      (.single ((physicalVal_arc D color c u v).mp ha))
  · intro c u v w huv hvw
    exact (physicalVal_reach D color c u w).mpr
      (((physicalVal_reach D color c u v).mp huv).trans
        ((physicalVal_reach D color c v w).mp hvw))
  · intro c i hr
    exact hmiss i ⟨c, (physicalVal_reach D color c (finRotate n i) i).mp hr⟩
  · intro i
    exact (physicalVal_arc D color (word i) i (finRotate n i)).mpr (hcycle i)
  · intro a b c u v w hab hbc hca huv hvw hwu
    rintro ⟨ha, hb, hc⟩
    rcases (physicalVal_arc D color a u v).mp ha with ⟨hDuv, hCuv⟩
    rcases (physicalVal_arc D color b v w).mp hb with ⟨hDvw, hCvw⟩
    rcases (physicalVal_arc D color c w u).mp hc with ⟨hDwu, hCwu⟩
    apply hno
    exact ⟨u, v, w, huv, hvw, hwu, hDuv, hDvw, hDwu,
      hCuv.trans_ne (hCvw ▸ hab), hCvw.trans_ne (hCwu ▸ hbc), hCwu.trans_ne (hCuv ▸ hca)⟩

end OPG1808CNF
end

section

open OPG1808 ModuleOPG1808CNF

namespace OPG1808Cuts

variable {n : ℕ} [NeZero n]

/-- Selector truth is precisely a path of the selected color in the induced
cyclic interval. It is not inferred from a merely abstract Boolean model. -/
def IntervalPath (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (d : ℕ) (u : Fin n) (k : Fin 3) : Prop :=
  Relation.ReflTransGen
    (fun a b : Fin (d + 3) ↦ D (cyclicVertex u a.val) (cyclicVertex u b.val) ∧
      color (cyclicVertex u a.val) (cyclicVertex u b.val) = k)
    0 (Fin.last (d + 2))

/-- Extend only beyond the finite prefix block. The old unbounded `LexModel`
continues to describe `base`, while `CutModel` describes this valuation. -/
def cutVal (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (base : Sat.Valuation) : Sat.Valuation :=
  fun i ↦ if i < selectorBase n then base i else
    ∃ (d : ℕ) (u : Fin n) (k : Fin 3),
      selectorCode (d + 3) u k = i ∧ IntervalPath D color d u k

theorem cutVal_below (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (base : Sat.Valuation) (i : ℕ) (hi : i < selectorBase n) :
    cutVal D color base i ↔ base i := by
  simp only [cutVal, if_pos hi]

theorem cutVal_arc (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (base : Sat.Valuation) (k : Fin 3) (u v : Fin n) :
    cutVal D color base (arcCode k u v) ↔ base (arcCode k u v) :=
  cutVal_below D color base _ (lt_of_lt_of_le (arcCode_lt k u v)
    (Nat.le_add_right _ _))

theorem cutVal_reach (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (base : Sat.Valuation) (k : Fin 3) (u v : Fin n) :
    cutVal D color base (reachCode k u v) ↔ base (reachCode k u v) :=
  cutVal_below D color base _ (lt_of_lt_of_le (reachCode_lt k u v)
    (Nat.le_add_right _ _))

theorem selectorCode_injective (d e : ℕ) (u v : Fin n) (k l : Fin 3)
    (h : selectorCode (d + 3) u k = selectorCode (e + 3) v l) :
    d = e ∧ u = v ∧ k = l := by
  have hf : ∀ (d : ℕ) (u : Fin n) (k : Fin 3),
      selectorCode (d + 3) u k = selectorBase n + 3 * (n * d + u.val) + k.val := by
    intro d u k
    simp only [selectorCode, Nat.add_sub_cancel_right, Nat.mul_add, Nat.mul_assoc,
      Nat.add_assoc]
  rw [hf, hf] at h
  have hpair : n * d + u.val = n * e + v.val := by omega
  have hk : k = l := Fin.ext (by omega)
  have hd := congrArg (fun x : ℕ ↦ x / n) hpair
  rw [Nat.add_comm (n * d), Nat.add_comm (n * e),
    Nat.add_mul_div_left _ _ (NeZero.pos n),
    Nat.add_mul_div_left _ _ (NeZero.pos n),
    Nat.div_eq_of_lt u.isLt, Nat.div_eq_of_lt v.isLt, Nat.zero_add, Nat.zero_add] at hd
  refine ⟨hd, Fin.ext ?_, hk⟩
  rw [hd] at hpair
  exact Nat.add_left_cancel hpair

theorem cutVal_selector (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (base : Sat.Valuation) (d : ℕ) (u : Fin n) (k : Fin 3) :
    cutVal D color base (selectorCode (d + 3) u k) ↔ IntervalPath D color d u k := by
  have hge : ¬selectorCode (d + 3) u k < selectorBase n := by
    dsimp [selectorCode]
    omega
  rw [cutVal, if_neg hge]
  constructor
  · rintro ⟨e, v, l, heq, hp⟩
    obtain ⟨rfl, rfl, rfl⟩ := selectorCode_injective e d v u l k heq
    exact hp
  · exact fun hp ↦ ⟨d, u, k, rfl, hp⟩

theorem cyclicVertex_zero (u : Fin n) : cyclicVertex u 0 = u := by
  simp only [cyclicVertex, Fin.ofNat_zero, add_zero]

/-- Injectivity holds for every interval no longer than the ambient cycle. -/
theorem cyclicVertex_injective (length : ℕ) (hlen : length ≤ n) (u : Fin n) :
    Function.Injective (fun j : Fin length ↦ cyclicVertex u j.val) := by
  intro a b hab
  have hc : Fin.ofNat n a.val = Fin.ofNat n b.val := add_left_cancel hab
  apply Fin.ext
  have hv := congrArg Fin.val hc
  simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hlen),
    Nat.mod_eq_of_lt (lt_of_lt_of_le b.isLt hlen)] using hv

theorem cyclicVertex_succ (d : ℕ) (u : Fin n) (j : Fin (d + 2)) :
    cyclicVertex u j.succ.val = finRotate n (cyclicVertex u j.castSucc.val) := by
  rw [finRotate_apply]
  change u + Fin.ofNat n (j.val + 1) = (u + Fin.ofNat n j.val) + 1
  rw [add_assoc]
  congr 1
  apply Fin.ext
  simp only [Fin.val_ofNat, Fin.val_add, Fin.val_one']
  exact Nat.add_mod _ _ _

/-- Explicit external source bound. This lemma does not assume a bound-eight
theorem: the supplied bound can later be instantiated by any accepted result. -/
theorem intervalPath_exists_of_source_bound
    (bound : ℕ) (hbound : bound ≤ n)
    (sourceBound : ∀ (m : ℕ), 0 < m → m ≤ bound →
      ∀ (E : Digraph (Fin m)) (c : ArcColoring (Fin m)),
        IsTournament E → ¬HasRainbowDirectedTriangle E c →
          ∃ s : Fin m, IsMonochromaticSource E c s)
    (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hmissing : ∀ j : Fin n,
      ¬MonochromaticallyReaches D color (finRotate n j) j)
    (d : ℕ) (hd : d + 3 ≤ bound) (u : Fin n) :
    ∃ k : Fin 3, IntervalPath D color d u k := by
  let e : Fin (d + 3) → Fin n := fun j ↦ cyclicVertex u j.val
  let E : Digraph (Fin (d + 3)) := fun a b ↦ D (e a) (e b)
  let c : ArcColoring (Fin (d + 3)) := fun a b ↦ color (e a) (e b)
  have he := cyclicVertex_injective (d + 3) (le_trans hd hbound) u
  obtain ⟨s, hs⟩ := sourceBound (d + 3) (by omega) hd E c
    (OPG1808Audit.is_tournament_map D e he ht)
    (OPG1808Audit.no_rainbow_map D color e he hno)
  have hs0 : s = 0 := by
    have honly : ∀ s : Fin (d + 3), IsMonochromaticSource E c s → s = 0 := by
      intro s
      refine Fin.cases (fun _ ↦ rfl) (fun j hj ↦ ?_) s
      have hp := OPG1808Audit.monochromatically_reaches_map D color e (hj j.castSucc)
      have hstep : e j.succ = finRotate n (e j.castSucc) := cyclicVertex_succ d u j
      rw [hstep] at hp
      exact False.elim (hmissing (e j.castSucc) hp)
    exact honly s hs
  subst s
  exact hs (Fin.last (d + 2))

/-- Physical construction from a genuine source theorem and physical meanings
for base arc/reach atoms. The base may independently carry the full LexModel. -/
theorem physical_cut_model
    (bound : ℕ) (hbound : bound ≤ n)
    (sourceBound : ∀ (m : ℕ), 0 < m → m ≤ bound →
      ∀ (E : Digraph (Fin m)) (c : ArcColoring (Fin m)),
        IsTournament E → ¬HasRainbowDirectedTriangle E c →
          ∃ s : Fin m, IsMonochromaticSource E c s)
    (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hmissing : ∀ j : Fin n,
      ¬MonochromaticallyReaches D color (finRotate n j) j)
    (base : Sat.Valuation)
    (harc : ∀ (k : Fin 3) (u v : Fin n),
      base (arcCode k u v) ↔ D u v ∧ color u v = k)
    (hreach : ∀ (k : Fin 3) (u v : Fin n),
      base (reachCode k u v) ↔
        Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k) u v) :
    CutModel (n := n) bound (cutVal D color base) := by
  have hex := intervalPath_exists_of_source_bound bound hbound sourceBound
    D color ht hno hmissing
  have hmap : ∀ (d : ℕ) (u : Fin n) (k : Fin 3), IntervalPath D color d u k →
      Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k)
        u (cyclicVertex u (d + 2)) := by
    intro d u k hp
    dsimp only [IntervalPath] at hp
    have hp' : Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k)
        (cyclicVertex u (0 : Fin (d + 3)).val)
        (cyclicVertex u (Fin.last (d + 2)).val) :=
      hp.lift (p := fun a b ↦ D a b ∧ color a b = k)
        (fun j : Fin (d + 3) ↦ cyclicVertex u j.val) (fun _ _ h ↦ h)
    simpa only [Fin.val_zero, cyclicVertex_zero, Fin.val_last] using hp'
  constructor
  · intro u d hlo hhi
    obtain ⟨k, hk⟩ := hex (d - 2) (by omega) u
    refine ⟨k, (cutVal_reach D color base k _ _).mpr ((hreach k _ _).mpr ?_)⟩
    have heq : d - 2 + 2 = d := by omega
    simpa only [heq] using hmap (d - 2) u k hk
  · intro d hd u
    obtain ⟨k, hk⟩ := hex d hd u
    exact ⟨k, (cutVal_selector D color base d u k).mpr hk⟩
  · intro d _ u k hk
    exact (cutVal_reach D color base k _ _).mpr ((hreach k _ _).mpr
      (hmap d u k ((cutVal_selector D color base d u k).mp hk)))
  · intro d _ u k S hs ht' hk
    obtain ⟨a, b, ha, hb, hab⟩ := OPG1808Intervals.colored_path_crosses_cut
      (fun a b : Fin (d + 3) ↦ D (cyclicVertex u a.val) (cyclicVertex u b.val))
      (fun a b : Fin (d + 3) ↦ color (cyclicVertex u a.val) (cyclicVertex u b.val))
      k ((cutVal_selector D color base d u k).mp hk) S hs ht'
    exact ⟨a, b, ha, hb, (cutVal_arc D color base k _ _).mpr ((harc k _ _).mpr hab)⟩

/-- The bound-seven instance is discharged by the already accepted theorem. -/
theorem physical_cut_model_seven
    (hn : 7 ≤ n)
    (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hmissing : ∀ j : Fin n,
      ¬MonochromaticallyReaches D color (finRotate n j) j)
    (base : Sat.Valuation)
    (harc : ∀ (k : Fin 3) (u v : Fin n),
      base (arcCode k u v) ↔ D u v ∧ color u v = k)
    (hreach : ∀ (k : Fin 3) (u v : Fin n),
      base (reachCode k u v) ↔
        Relation.ReflTransGen (fun a b ↦ D a b ∧ color a b = k) u v) :
    CutModel (n := n) 7 (cutVal D color base) := by
  apply physical_cut_model 7 hn _ D color ht hno hmissing base harc hreach
  intro m hm hseven E c hE hnoE
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact OPG1808.order_seven E c hE (by simpa only [Fintype.card_fin] using hseven) hnoE

/-- Concrete base valuation used by the existing lexicographic schemas. -/
def physicalLexVal (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (word : Fin n → Fin 3) (rot : ℕ → Fin n) (perm : ℕ → Equiv.Perm (Fin 3)) :
    Sat.Valuation := extendedVal word rot perm (OPG1808CNF.physicalVal D color)

/-- Fully physical bound-seven instance, with no semantic atom premises. -/
theorem physical_extended_cut_model_seven
    (hn : 7 ≤ n)
    (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (word : Fin n → Fin 3) (rot : ℕ → Fin n) (perm : ℕ → Equiv.Perm (Fin 3))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hmissing : ∀ j : Fin n,
      ¬MonochromaticallyReaches D color (finRotate n j) j) :
    CutModel (n := n) 7 (cutVal D color (physicalLexVal D color word rot perm)) := by
  apply physical_cut_model_seven hn D color ht hno hmissing
  · intro k u v
    change extendedVal word rot perm (OPG1808CNF.physicalVal D color) (arcCode k u v) ↔ _
    rw [extendedVal_arc]
    exact OPG1808CNF.physicalVal_arc D color k u v
  · intro k u v
    change extendedVal word rot perm (OPG1808CNF.physicalVal D color) (reachCode k u v) ↔ _
    rw [extendedVal_reach]
    exact OPG1808CNF.physicalVal_reach D color k u v

omit [NeZero n] in
/-- The unchanged LexModel belongs to the base valuation, alongside the
CutModel above on its finite extension. -/
theorem physical_extended_lex_model
    (hn : 2 ≤ n)
    (D : Digraph (Fin n)) (color : ArcColoring (Fin n))
    (word : Fin n → Fin 3) (rot : ℕ → Fin n) (perm : ℕ → Equiv.Perm (Fin 3))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin n, D i (finRotate n i) ∧ color i (finRotate n i) = word i)
    (hmissing : ∀ j : Fin n,
      ¬MonochromaticallyReaches D color (finRotate n j) j)
    (hmin : PrefixMinimal word) :
    LexModel word rot perm (physicalLexVal D color word rot perm) := by
  have : NeZero (n - 1) := ⟨by omega⟩
  have h := OPG1808CNF.physical_model D color word ht hno hcycle hmissing
  apply extended_model (base := OPG1808CNF.physicalVal D color) _ hmin rot perm
  exact
    { orientation := h.orientation
      color_exclusive := h.color_exclusive
      direction_exclusive := h.direction_exclusive
      arc_reach := h.arc_reach
      reach_trans := h.reach_trans
      predecessor_forbidden := h.predecessor_forbidden
      cycle := h.cycle
      rainbow_forbidden := h.rainbow_forbidden }

end OPG1808Cuts
end

section




namespace ModuleOPG1808Certificate

/-- Metadata for the rotation/palette order in the independent Python generator.
The identity transform at rotation zero is skipped. -/
def lexRot (n : Nat) [NeZero n] (t : Nat) : Fin n :=
  ⟨((t + 1) / 6) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

def lexPerm (t : Nat) : Equiv.Perm (Fin 3) :=
  match (t + 1) % 6 with
  | 0 => Equiv.refl _
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 0 1
  | 3 => (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  | 4 => (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  | _ => Equiv.swap 0 2

end ModuleOPG1808Certificate
end

section

open OPG1808

namespace OPG1808PhysicalPrefix

/-- A purely physical cycle conclusion obtained from the explicitly supplied
Boolean exclusion. The raw premise is discharged inside each complete packet;
it does not appear in the public cycle theorem's signature. -/
theorem predecessor_reachable_of_cut_exclusion
    (P : (Fin 8 → Fin 3) → Prop)
    (hexclude : ∀ (word : Fin 8 → Fin 3) (base val : Sat.Valuation),
      ModuleOPG1808CNF.LexModel word (ModuleOPG1808Certificate.lexRot 8)
        ModuleOPG1808Certificate.lexPerm base →
      (∀ i, i < OPG1808Cuts.selectorBase 8 → (val i ↔ base i)) →
      OPG1808Cuts.CutModel (n := 8) 7 val → P word → False)
    (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin 8, D i (finRotate 8 i))
    (hminimal : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex (fun i ↦ color i (finRotate 8 i)) ≤
        toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r)))))
    (hprefix : P (fun i ↦ color i (finRotate 8 i))) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  classical
  by_contra hbad
  have hmissing : ∀ i : Fin 8,
      ¬MonochromaticallyReaches D color (finRotate 8 i) i := by
    intro i hi
    exact hbad ⟨i, hi⟩
  let word : Fin 8 → Fin 3 := fun i ↦ color i (finRotate 8 i)
  have hlex : ModuleOPG1808CNF.PrefixMinimal word := by
    intro r σ i hp
    exact Pi.apply_le_of_toLex (hminimal r σ) hp
  let base : Sat.Valuation := OPG1808Cuts.physicalLexVal D color word
    (ModuleOPG1808Certificate.lexRot 8) ModuleOPG1808Certificate.lexPerm
  let val : Sat.Valuation := OPG1808Cuts.cutVal D color base
  exact hexclude word base val
    (OPG1808Cuts.physical_extended_lex_model (by decide) D color word
      (ModuleOPG1808Certificate.lexRot 8) ModuleOPG1808Certificate.lexPerm
      htournament hnoRainbow (fun i ↦ ⟨hcycle i, rfl⟩) hmissing hlex)
    (OPG1808Cuts.cutVal_below D color base)
    (OPG1808Cuts.physical_extended_cut_model_seven (by decide) D color word
      (ModuleOPG1808Certificate.lexRot 8) ModuleOPG1808Certificate.lexPerm
      htournament hnoRainbow hmissing) hprefix


end OPG1808PhysicalPrefix
end

section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OPG1808CutCertificates
open ModuleOPG1808Certificate
lrat_proof cert_n8_b7_p0011
 "p cnf 445 950\n-376 144 139 159 153 0\n-387 237 0\n-276 -298 279 0\n-379 152 147 111 105 0\n36 43 89 96 144 151 0\n-445 318 0\n-337 -67 -153 338 0\n-424 157 108 115 121 128 0\n-237 -261 233 0\n-279 -317 276 0\n-355 144 145 0\n-444 103 56 63 68 75 82 0\n-301 -282 303 0\n-122 283 0\n-213 -226 214 0\n-140 300 0\n-53 -122 -31 0\n-391 132 139 146 153 0\n-373 298 0\n-323 -8 -74 324 0\n1 52 105 0\n-296 -305 298 0\n-275 -290 277 0\n-444 100 101 103 53 54 56 60 61 63 80 81 82 0\n-41 -130 0\n67 0\n-2 -74 -132 0\n-69 -93 0\n-28 -145 -102 0\n-15 175 0\n-409 120 121 122 123 124 0\n-268 -291 271 0\n-93 -148 0\n-251 -263 249 0\n-2 162 0\n-30 192 0\n-101 -131 0\n170 221 276 0\n-138 298 0\n-234 -244 237 0\n-211 -198 212 0\n-287 -278 291 0\n-65 224 0\n-261 -226 262 0\n-192 -209 189 0\n-121 -134 0\n392 393 394 0\n-64 -152 -46 0\n-1 -136 330 0\n-70 -100 0\n-253 -222 257 0\n-42 204 0\n-256 -242 257 0\n-175 0\n-184 -201 181 0\n-430 113 116 117 118 127 129 130 131 134 136 137 138 0\n-105 -105 0\n-425 3 4 5 10 11 12 17 18 19 23 24 25 0\n-425 5 12 19 25 29 36 0\n-352 297 0\n-21 180 0\n-437 37 31 32 34 44 38 39 41 20 14 15 16 0\n-336 -8 -44 337 0\n-403 270 0\n-184 -202 182 0\n185 237 292 0\n-144 304 0\n-399 262 0\n-220 -231 219 0\n-87 247 0\n-36 -144 0\n-317 -296 318 0\n428 429 430 0\n-1 -118 -98 0\n-19 -97 -155 0\n425 426 427 0\n-333 -8 -44 334 0\n-405 60 61 64 80 81 83 87 88 89 0\n-48 -131 0\n-181 -168 182 0\n-296 -302 295 0\n-58 218 0\n-143 303 0\n-313 -271 319 0\n-210 -191 212 0\n-430 116 118 122 124 129 131 136 138 151 152 0\n-429 60 61 64 65 80 81 83 84 87 88 89 90 0\n-9 -61 0\n-331 -67 -152 0\n-294 -275 295 0\n-75 235 0\n173 224 279 0\n-309 -292 312 0\n-111 272 0\n-408 70 77 84 90 97 0\n-313 -269 317 0\n-268 -290 270 0\n-96 257 0\n-67 -120 0\n-404 172 0\n-61 220 0\n-1 -63 -139 0\n-75 -129 0\n-92 -117 0\n-314 -278 319 0\n-169 -185 173 0\n-353 199 0\n-224 -259 219 0\n-360 52 53 54 0\n-200 -164 205 0\n44 51 97 104 152 159 0\n-243 -254 240 0\n-434 188 0\n-107 268 0\n-88 248 0\n-114 275 0\n-292 -317 289 0\n-202 -177 205 0\n-4 -90 -153 0\n-378 92 99 52 0\n-1 -61 -125 0\n-258 -260 253 0\n-371 192 0\n-366 68 75 82 0\n-318 -304 319 0\n-67 -130 -40 0\n-258 -264 257 0\n-330 -8 -144 331 0\n-183 -198 184 0\n-269 -294 266 0\n-433 128 126 143 140 150 147 157 154 108 105 0\n-77 -131 0\n-62 -115 0\n4 31 56 85 109 139 0\n-431 181 0\n-1 -36 336 0\n74 0\n-433 128 130 131 126 143 144 145 140 108 110 111 105 0\n-178 -206 179 0\n-279 -315 274 0\n-208 -177 211 0\n-1 -28 328 0\n-116 277 0\n-362 170 0\n-356 45 46 0\n-353 37 44 0\n-276 -293 273 0\n-306 -270 311 0\n-244 -262 241 0\n-139 299 0\n-263 -238 259 0\n-74 -135 0\n210 263 317 0\n-131 -156 0\n-230 -260 225 0\n-103 264 0\n-437 34 41 48 2 9 16 0\n-261 -229 265 0\n-390 82 83 84 78 0\n-380 10 11 17 18 23 24 0\n-278 -306 273 0\n-221 -244 224 0\n-430 113 114 115 116 117 118 0\n-418 301 0\n-315 -282 317 0\n-419 41 48 2 9 16 0\n-213 -230 218 0\n-43 205 0\n-52 -52 0\n-9 -114 0\n-117 278 0\n-381 60 63 73 75 80 82 0\n-273 0\n-315 -284 319 0\n-1 -64 -146 0\n-102 263 0\n-424 317 0\n-436 134 141 148 155 106 113 0\n-364 276 0\n353 354 355 0\n-178 -200 174 0\n-435 240 0\n-314 -277 318 0\n-437 37 34 44 41 6 2 13 9 20 16 0\n-203 -183 205 0\n-16 -67 0\n-238 -214 241 0\n-125 286 0\n-59 219 0\n-187 -169 189 0\n-137 -97 -49 0\n-377 201 0\n-388 131 138 145 152 0\n-252 -213 254 0\n-199 -210 197 0\n-263 -243 265 0\n-74 -128 0\n-400 316 0\n-413 30 26 27 37 31 32 44 38 39 0\n-444 99 103 52 56 66 68 72 75 79 82 0\n-188 -177 190 0\n-370 128 130 143 144 0\n-56 216 0\n-396 93 100 53 60 0\n-9 -130 -92 0\n-369 76 83 89 0\n-277 -302 275 0\n2 21 54 71 107 125 0\n-221 -243 223 0\n-355 145 152 0\n-346 -28 -67 347 0\n-214 -235 216 0\n-390 238 0\n-251 -259 245 0\n-186 -162 189 0\n-429 65 70 77 84 90 97 0\n-316 -291 319 0\n-439 144 140 142 159 154 156 110 105 107 123 119 120 0\n-265 0\n-204 -190 205 0\n-63 -140 0\n-439 140 142 147 149 154 156 105 107 119 120 0\n-429 60 61 62 63 64 65 0\n-237 -260 232 0\n-91 252 0\n-268 -292 272 0\n183 235 290 0\n-421 147 149 154 156 105 107 119 120 0\n-384 69 76 83 89 0\n-389 186 0\n-303 0\n-282 -294 280 0\n-176 -192 179 0\n362 363 364 0\n-287 -274 288 0\n-39 -147 0\n410 411 412 0\n-214 -236 217 0\n-410 180 0\n-252 -216 257 0\n-408 69 70 76 77 83 84 89 90 0\n431 432 433 0\n-119 280 0\n-180 -160 181 0\n-227 -244 230 0\n-25 184 0\n-190 -198 191 0\n-1 -112 0\n-67 -127 0\n-170 -186 167 0\n-286 -269 289 0\n386 387 388 0\n-286 -267 288 0\n-201 -169 203 0\n-260 -220 262 0\n-441 97 91 92 93 94 95 0\n-316 -290 318 0\n-252 -214 255 0\n-51 212 0\n-116 -36 -92 0\n211 264 318 0\n-201 -171 205 0\n178 229 284 0\n36 89 144 0\n13 46 65 99 118 154 0\n-353 36 37 0\n-17 -121 0\n-433 129 131 126 136 138 133 151 152 147 109 111 105 0\n-72 232 0\n-158 318 0\n-244 -261 240 0\n389 390 391 0\n24 34 75 88 129 142 0\n-255 -235 257 0\n-384 229 0\n-351 243 0\n-367 120 121 122 0\n-164 -199 166 0\n-305 -313 299 0\n-298 -313 293 0\n-324 -67 -136 325 0\n-241 0\n-4 -144 -91 0\n-83 -95 0\n-297 -312 298 0\n416 417 418 0\n-62 -30 -154 0\n-441 97 91 93 94 95 65 59 60 61 62 0\n204 256 310 0\n-208 -178 212 0\n-358 154 105 0\n-171 -199 173 0\n-277 -299 273 0\n-243 -258 244 0\n-380 171 0\n-284 -307 280 0\n-183 -194 181 0\n-193 -163 197 0\n-308 -283 311 0\n-53 -18 -139 0\n-67 226 0\n-74 -29 -149 0\n-291 -312 292 0\n-160 -170 163 0\n-161 -179 166 0\n413 414 415 0\n-309 -290 311 0\n-35 197 0\n-94 255 0\n-39 -64 0\n-294 -277 296 0\n177 228 283 0\n-84 244 0\n-8 -123 -92 0\n-76 -130 0\n-287 -276 289 0\n-31 -139 0\n-85 245 0\n-130 -44 -101 0\n-407 179 0\n-245 -215 249 0\n-55 -132 0\n-7 167 0\n-177 -193 174 0\n-1 160 0\n-66 225 0\n-429 60 61 63 64 65 80 81 82 83 84 0\n-290 -301 288 0\n209 262 316 0\n-405 223 0\n-398 45 46 48 14 15 16 0\n-362 10 17 23 0\n-429 60 65 73 77 80 84 87 90 93 97 0\n-185 -207 181 0\n-160 -173 166 0\n-297 -307 294 0\n-177 -199 179 0\n-245 -213 247 0\n-284 -309 281 0\n-98 259 0\n-77 -156 0\n-221 -238 219 0\n-432 232 0\n-226 -236 229 0\n-433 126 133 140 147 154 105 0\n-54 -125 0\n-387 76 77 83 84 89 90 0\n-307 -275 309 0\n-350 29 36 0\n163 215 269 0\n-298 -314 294 0\n-63 222 0\n-93 254 0\n-80 240 0\n-219 0\n-438 248 0\n-12 -152 -99 0\n440 441 442 0\n-149 309 0\n-383 178 0\n-271 -312 272 0\n-39 201 0\n-108 -29 -91 0\n-24 183 0\n-290 -305 292 0\n-317 -297 319 0\n-338 -74 -1 0\n-79 239 0\n-101 262 0\n-268 -287 266 0\n-223 -252 219 0\n192 244 298 0\n-236 -253 232 0\n-207 -171 211 0\n-67 -131 -47 0\n359 360 361 0\n-294 -278 297 0\n-1 -62 -132 0\n-433 129 130 131 126 136 137 138 133 109 110 111 105 0\n-341 -8 -97 342 0\n-189 0\n11 32 63 86 116 140 0\n-441 97 93 94 95 58 53 54 55 65 60 61 62 0\n-248 -234 249 0\n-285 -314 280 0\n-177 -198 178 0\n-319 0\n-428 173 0\n6 45 58 98 111 153 0\n-46 -154 0\n-49 210 0\n-74 -28 -142 0\n-10 -27 0\n-9 -76 -147 0\n-247 -227 249 0\n-441 92 93 94 95 99 100 101 102 52 53 54 55 0\n-117 -147 0\n-129 -36 -94 0\n-304 -310 303 0\n-57 217 0\n-439 144 145 139 141 142 117 118 112 113 114 0\n-148 308 0\n-1 -144 339 0\n-444 98 99 100 101 102 103 0\n-412 128 125 143 139 150 146 157 153 0\n-178 -201 175 0\n-83 -150 0\n-31 -109 0\n-61 -24 -140 0\n-64 -92 0\n-170 -191 172 0\n-445 155 156 157 158 106 107 108 109 113 114 115 116 0\n-123 284 0\n-305 -317 303 0\n-76 -94 0\n-183 -195 182 0\n-36 198 0\n-56 -36 -146 0\n-146 306 0\n-11 171 0\n-90 251 0\n-190 -193 186 0\n-210 -190 211 0\n-70 230 0\n-218 0\n-187 -171 190 0\n-200 -161 202 0\n-433 129 126 136 133 151 147 158 154 109 105 0\n-344 -67 -1 345 0\n-44 -152 0\n395 396 397 0\n-340 -67 -153 0\n-200 -160 201 0\n-115 -133 0\n-91 -146 0\n-12 -97 -154 0\n-277 -305 279 0\n-18 -33 0\n-411 231 0\n-157 317 0\n-385 120 123 135 137 142 144 0\n-37 199 0\n-260 -223 265 0\n-2 -77 -153 0\n-433 131 126 138 133 145 140 152 147 111 105 0\n350 351 352 0\n-408 230 0\n-46 -118 0\n-68 228 0\n-4 164 0\n-12 -64 0\n-350 191 0\n-107 -125 0\n-63 -145 -46 0\n-201 -168 202 0\n-430 115 116 117 118 121 122 123 124 128 129 130 131 0\n30 49 84 102 138 157 0\n-365 17 18 23 24 0\n19 40 69 93 123 148 0\n-264 -250 265 0\n-8 -70 -154 0\n-166 0\n-361 268 0\n-243 -255 241 0\n-168 -177 171 0\n-183 -193 180 0\n-300 -279 305 0\n-141 301 0\n-348 -8 -1 349 0\n-207 -168 208 0\n-325 -74 -89 0\n-275 -292 279 0\n-382 277 0\n18 33 68 87 122 141 0\n-36 -152 -103 0\n-68 -145 -47 0\n-9 -74 -133 0\n-287 -277 290 0\n-2 -54 0\n25 41 76 94 130 149 0\n-64 -147 0\n20 47 70 100 124 155 0\n-401 4 11 18 24 28 0\n-416 36 37 31 32 33 0\n-345 -74 -8 346 0\n-8 168 0\n-37 -103 0\n-92 253 0\n443 444 445 0\n-92 -147 0\n-1 -36 333 0\n-151 311 0\n-121 -30 -100 0\n-69 -44 -155 0\n-244 -264 242 0\n-75 -144 -41 0\n-413 29 26 27 36 31 32 51 45 46 0\n-56 -37 -153 0\n-122 -37 -100 0\n-8 -68 -140 0\n-385 120 122 123 135 136 137 0\n-106 267 0\n-433 128 130 126 143 144 140 157 159 154 108 110 105 0\n-279 -318 277 0\n-32 -140 0\n-310 -298 312 0\n-29 -150 0\n-313 -268 316 0\n-122 -36 -93 0\n-194 -170 197 0\n-8 -124 -99 0\n-322 -74 -89 0\n-77 237 0\n-76 -149 0\n-9 169 0\n-342 -67 -98 0\n-36 -97 -158 0\n-351 83 89 0\n-10 170 0\n-226 -232 225 0\n-62 -133 0\n-8 -67 -126 0\n-182 0\n-350 28 29 0\n-69 -152 -47 0\n-278 -308 274 0\n-259 -216 264 0\n-55 215 0\n-433 128 130 131 125 126 143 144 145 139 140 0\n-254 -230 258 0\n-3 163 0\n-430 279 0\n398 399 400 0\n-2 -130 -91 0\n-357 260 0\n-412 125 132 139 146 153 0\n179 230 285 0\n-279 -316 275 0\n-370 291 0\n-207 -170 210 0\n-63 -37 -154 0\n-83 243 0\n-290 -299 286 0\n-233 0\n-53 213 0\n-205 0\n-124 285 0\n-171 -193 167 0\n-63 -36 -147 0\n-304 -308 301 0\n-132 293 0\n-370 128 129 130 0\n-412 128 129 130 131 125 0\n-28 -136 0\n44 97 152 0\n-374 31 38 45 0\n-443 211 0\n-266 -279 272 0\n-386 185 0\n-368 23 24 25 0\n-365 16 17 18 0\n-441 97 92 93 94 95 58 52 53 54 55 0\n-55 -30 -153 0\n-367 283 0\n-429 60 64 65 73 76 77 80 83 84 87 89 90 0\n-339 -8 -152 340 0\n-89 250 0\n-422 45 49 7 10 14 17 21 23 0\n-259 -217 265 0\n-115 276 0\n-1 -67 320 0\n-287 -279 292 0\n-44 -97 0\n-230 -264 228 0\n-12 172 0\n-402 216 0\n-394 300 0\n-270 -305 272 0\n-359 162 0\n377 378 379 0\n28 82 136 0\n-275 -291 278 0\n-109 270 0\n-375 245 0\n-269 -297 271 0\n-118 -154 0\n169 220 275 0\n-74 -81 0\n-227 -239 225 0\n-299 -268 302 0\n-28 190 0\n-419 203 0\n-307 -279 312 0\n-104 265 0\n-1 -65 -153 0\n-262 -235 264 0\n-18 177 0\n-186 -160 187 0\n-34 196 0\n-321 -67 -28 322 0\n383 384 385 0\n-1 -89 341 0\n-251 -262 248 0\n-251 -261 247 0\n-54 -71 0\n-415 294 0\n-76 236 0\n-240 -226 241 0\n-423 98 99 100 101 102 0\n-275 -286 273 0\n365 366 367 0\n-41 203 0\n-37 -90 0\n-427 271 0\n-121 282 0\n-379 147 154 105 0\n-401 164 0\n-40 202 0\n-155 315 0\n-174 -160 175 0\n-8 -69 -147 0\n-84 -138 0\n-295 0\n-9 -75 -140 0\n12 39 64 92 117 147 0\n-8 -113 0\n-46 207 0\n-25 -41 0\n-62 -136 -32 0\n-153 313 0\n-373 136 138 151 152 0\n-444 264 0\n-13 173 0\n-346 -136 -67 0\n-293 -270 296 0\n-74 -138 -48 0\n-307 -277 311 0\n-302 -289 303 0\n-154 314 0\n-280 0\n-160 -168 161 0\n-278 -312 279 0\n-97 -152 0\n-347 -144 -74 0\n434 435 436 0\n-8 -122 -86 0\n-100 261 0\n356 357 358 0\n-94 -149 0\n-433 128 131 126 143 145 140 150 152 147 108 111 105 0\n-1 -45 348 0\n-314 -275 316 0\n-172 -206 173 0\n-444 98 99 100 101 103 78 79 80 81 82 0\n-17 176 0\n-316 -287 314 0\n-152 312 0\n-328 -8 -36 329 0\n186 238 293 0\n-246 -221 249 0\n195 247 301 0\n-145 305 0\n-206 -210 204 0\n-385 120 121 122 123 0\n-423 263 0\n-366 228 0\n-150 310 0\n-68 -144 -40 0\n-356 207 0\n-28 -144 -95 0\n-74 -136 -34 0\n-226 -234 227 0\n-412 128 130 131 125 143 144 145 139 0\n-198 -200 193 0\n-283 -300 280 0\n-244 -260 239 0\n-213 -229 217 0\n-170 -192 173 0\n165 217 271 0\n-257 0\n-378 253 0\n-445 158 109 116 122 129 136 0\n371 372 373 0\n-177 -194 175 0\n-279 -313 273 0\n-258 -261 254 0\n-349 -67 -8 0\n-198 -201 194 0\n-32 194 0\n-67 -24 -141 0\n-310 -296 311 0\n407 408 409 0\n-256 -244 258 0\n422 423 424 0\n202 254 308 0\n-91 -110 0\n-137 297 0\n-243 -253 239 0\n-44 206 0\n401 402 403 0\n-259 -213 261 0\n-320 -60 -74 0\n-78 238 0\n-298 -318 296 0\n-433 128 129 131 126 150 151 152 147 108 109 111 105 0\n-261 -227 263 0\n-191 -203 189 0\n-136 -90 -49 0\n-69 229 0\n-409 285 0\n-130 291 0\n-440 204 0\n-429 224 0\n-238 -213 240 0\n-302 -291 304 0\n-300 -275 302 0\n-136 -37 -102 0\n-29 -97 -157 0\n-423 100 101 102 53 54 55 60 61 62 0\n-110 -44 -98 0\n437 438 439 0\n-282 -298 285 0\n-406 278 0\n29 42 83 95 137 150 0\n-359 2 9 16 0\n-74 234 0\n196 248 302 0\n-421 149 156 107 114 120 0\n-190 -196 189 0\n-61 -129 -32 0\n-400 156 107 114 120 0\n-67 -73 0\n-167 0\n-55 -28 -139 0\n-98 -153 0\n-327 -144 -98 0\n-381 222 0\n-214 -237 218 0\n-267 -285 272 0\n-130 -149 0\n-302 -287 300 0\n-414 239 0\n-99 260 0\n-199 -207 194 0\n-437 31 32 34 38 39 41 45 46 48 14 15 16 0\n-393 89 90 86 57 58 52 0\n-212 0\n-198 -204 197 0\n-223 -255 220 0\n-168 -176 170 0\n-114 -77 -46 0\n-385 284 0\n-293 -268 295 0\n-147 307 0\n-217 -258 218 0\n-77 -101 0\n-262 -236 265 0\n-176 -187 175 0\n-114 -74 -27 0\n-156 316 0\n-402 52 53 54 56 79 80 81 82 0\n-285 -318 283 0\n-227 -243 229 0\n-420 255 0\n-236 -254 233 0\n-262 -234 263 0\n-392 194 0\n-398 209 0\n-433 129 130 126 136 137 133 158 159 154 109 110 105 0\n10 27 62 79 115 133 0\n-159 319 0\n-433 129 130 125 126 136 137 132 133 158 159 153 154 0\n-288 0\n-374 193 0\n-372 244 0\n-372 83 84 89 90 0\n-84 -102 0\n-9 -77 -154 0\n-405 60 64 73 76 80 83 87 89 0\n-55 -108 0\n-321 -67 -82 0\n-286 -270 290 0\n-86 246 0\n-201 -170 204 0\n-62 -28 -140 0\n-363 60 61 62 0\n-335 -74 -1 0\n-25 -149 0\n-354 251 0\n-358 314 0\n-269 -298 272 0\n-369 236 0\n-439 302 0\n-62 -29 -147 0\n-31 193 0\n-445 156 157 158 107 108 109 114 115 116 120 121 122 0\n380 381 382 0\n-311 0\n-1 -117 -91 0\n-381 60 61 63 80 81 82 0\n-398 45 48 7 9 14 16 0\n-41 -94 0\n181 232 287 0\n-397 308 0\n-129 290 0\n-433 129 125 126 136 132 133 151 146 147 158 153 154 0\n-283 -302 281 0\n-416 37 31 32 33 44 38 39 40 0\n-399 99 100 101 52 53 54 0\n162 214 268 0\n-357 99 52 0\n-71 231 0\n-55 -78 0\n374 375 376 0\n-56 -139 0\n-312 -318 311 0\n404 405 406 0\n-223 -258 224 0\n-46 -99 0\n-197 0\n-225 0\n-6 166 0\n-365 177 0\n-136 -36 -95 0\n-325 -74 -144 326 0\n-320 -8 -74 321 0\n-1 -115 -78 0\n8 0\n-54 214 0\n9 22 61 72 114 126 0\n-329 -67 -44 0\n-433 128 129 130 131 125 126 0\n-388 128 131 143 145 150 152 0\n-64 223 0\n-20 179 0\n-422 210 0\n-61 -130 -39 0\n-377 44 38 39 0\n-439 142 149 156 107 114 120 0\n-75 -36 -149 0\n-368 23 25 35 36 0\n-216 -251 218 0\n-292 -315 288 0\n-406 113 116 117 127 129 130 134 136 137 0\n-396 254 0\n-207 -172 212 0\n-131 292 0\n-67 -129 -33 0\n-245 -214 248 0\n37 50 90 103 145 158 0\n-291 -308 288 0\n-22 181 0\n180 231 286 0\n-14 174 0\n-332 -74 -153 0\n-193 -165 198 0\n-411 76 77 71 83 84 78 89 90 85 0\n203 255 309 0\n-299 -269 303 0\n-26 186 0\n-130 -97 -48 0\n-133 294 0\n-23 -74 0\n-444 99 100 101 103 52 53 54 56 79 80 81 82 0\n184 236 291 0\n164 216 270 0\n-272 0\n-234 -243 236 0\n-334 -67 -98 335 0\n-62 221 0\n-108 269 0\n-326 -136 -44 327 0\n-261 -228 264 0\n-254 -226 255 0\n-211 -195 208 0\n-50 211 0\n-231 -213 233 0\n-142 302 0\n-262 -231 259 0\n-186 -165 191 0\n-54 -107 0\n-2 -131 -98 0\n-118 279 0\n-270 -302 268 0\n-97 258 0\n-93 -123 0\n-368 184 0\n-331 -67 -44 332 0\n-297 -309 295 0\n187 239 294 0\n-193 -162 196 0\n5 38 57 91 110 146 0\n-1 -67 323 0\n-387 75 76 77 82 83 84 0\n-5 -97 -153 0\n-215 -244 218 0\n-29 191 0\n-200 -163 204 0\n-38 200 0\n-40 -93 0\n-33 195 0\n-41 -76 0\n-48 209 0\n-244 -259 238 0\n-302 -286 299 0\n-74 -137 -41 0\n172 223 278 0\n-110 271 0\n-302 -292 305 0\n-326 -136 -97 0\n419 420 421 0\n-190 -199 192 0\n-162 -185 166 0\n-437 196 0\n-129 -37 -101 0\n-234 -238 231 0\n-68 -141 0\n-206 -211 205 0\n-209 -183 211 0\n-5 -152 -98 0\n-136 296 0\n-391 136 137 132 158 159 153 0\n-215 -243 217 0\n-298 -316 295 0\n-19 178 0\n-1 -97 343 0\n-442 310 0\n-417 247 0\n-254 -228 257 0\n-391 137 138 132 144 145 139 0\n-11 -144 -92 0\n-229 -253 225 0\n-285 -316 281 0\n-18 -144 -93 0\n-195 -176 197 0\n-395 44 38 39 40 0\n-343 -8 -98 344 0\n-61 -114 0\n-281 -287 280 0\n-433 128 129 130 131 126 108 109 110 111 105 0\n-391 293 0\n-313 -270 318 0\n-426 217 0\n-249 0\n-433 128 129 126 150 151 147 157 158 154 108 109 105 0\n-441 91 92 93 94 95 98 99 100 101 102 0\n368 369 370 0\n-202 -176 204 0\n-259 -214 262 0\n-184 -200 180 0\n"
 "951 -15 0 54 30 0\n952 -105 0 57 0\n953 -437 37 31 32 34 44 38 39 41 20 14 16 0 951 62 0\n954 -331 -152 0 26 89 0\n955 -120 0 26 99 0\n956 -130 -40 0 26 126 0\n957 -433 128 126 143 140 150 147 157 154 108 0 952 131 0\n958 -433 128 130 131 126 143 144 145 140 108 110 111 0 952 138 0\n959 -135 0 137 152 0\n960 -52 0 169 0\n961 1 0 960 952 21 0\n962 -64 -146 0 961 175 0\n963 -16 0 26 186 0\n964 -128 0 137 197 0\n965 -444 99 103 56 66 68 72 75 79 82 0 960 200 0\n966 -370 130 143 144 0 964 202 0\n967 -346 -28 347 0 26 211 0\n968 -439 144 140 142 159 154 156 110 107 123 119 0 952 955 218 0\n969 -439 140 142 147 149 154 156 107 119 0 952 955 222 0\n970 -421 147 149 154 156 107 119 0 952 955 228 0\n971 -143 0 231 83 0\n972 -112 0 961 248 0\n973 -127 0 26 249 0\n974 -433 129 131 126 136 138 133 151 152 147 109 111 0 952 268 0\n975 -367 121 122 0 955 277 0\n976 -324 -136 325 0 26 281 0\n977 -358 154 0 952 291 0\n978 -277 -299 0 173 293 0\n979 226 0 26 301 0\n980 -29 -149 0 137 302 0\n981 160 0 961 325 0\n982 -398 45 46 48 14 0 951 963 331 0\n983 -173 166 0 981 335 0\n984 -236 229 0 979 344 0\n985 -433 126 133 140 147 154 0 952 345 0\n986 -59 0 355 189 0\n987 -338 0 137 961 367 0\n988 -223 -252 0 355 371 0\n989 -131 -47 0 26 375 0\n990 -62 -132 0 961 378 0\n991 -433 129 130 131 126 136 137 138 133 109 110 111 0 952 379 0\n992 -28 -142 0 137 392 0\n993 -441 92 93 94 95 99 100 101 102 53 54 55 0 960 396 0\n994 -304 -310 0 231 399 0\n995 -439 144 145 139 141 142 117 118 113 114 0 972 401 0\n996 -144 339 0 961 403 0\n997 -412 125 139 150 146 157 153 0 964 971 405 0\n998 -178 -201 0 54 406 0\n999 -305 -317 0 231 414 0\n1000 -58 0 425 82 0\n1001 -433 129 126 136 133 151 147 158 154 109 0 952 428 0\n1002 -344 345 0 26 961 429 0\n1003 -340 -153 0 26 432 0\n1004 -200 201 0 981 433 0\n1005 -385 123 137 142 144 0 955 959 441 0\n1006 -260 -223 0 219 443 0\n1007 -433 131 126 138 133 145 140 152 147 111 0 952 445 0\n1008 -430 115 116 117 118 121 122 123 124 129 130 131 0 964 456 0\n1009 -264 -250 0 219 460 0\n1010 -173 0 462 983 0\n1011 -428 0 1010 388 0\n1012 -243 -255 0 282 464 0\n1013 -348 -8 349 0 961 469 0\n1014 -325 -89 0 137 471 0\n1015 -9 -133 0 137 477 0\n1016 -345 -8 346 0 137 485 0\n1017 -36 333 0 961 491 0\n1018 -385 122 123 136 137 0 955 959 501 0\n1019 -433 130 126 144 140 157 159 154 108 110 0 964 971 952 503 0\n1020 -322 -89 0 137 512 0\n1021 -342 -98 0 26 516 0\n1022 -232 225 0 979 520 0\n1023 -8 -126 0 26 522 0\n1024 -433 130 131 125 126 144 145 139 140 0 964 971 529 0\n1025 -43 0 546 168 0\n1026 -370 129 130 0 964 552 0\n1027 -412 129 130 131 125 0 964 553 0\n1028 -365 17 18 0 963 561 0\n1029 -441 97 92 93 94 95 53 54 55 0 1000 960 562 0\n1030 -259 -217 0 219 569 0\n1031 320 0 961 26 571 0\n1032 -81 0 137 588 0\n1033 -104 0 219 594 0\n1034 -65 -153 0 961 595 0\n1035 -186 187 0 981 598 0\n1036 -321 -28 322 0 26 600 0\n1037 -89 341 0 961 602 0\n1038 -240 0 979 282 608 0\n1039 -435 0 1038 182 0\n1040 -80 0 1038 354 0\n1041 -275 -286 0 173 610 0\n1042 -379 147 154 0 952 616 0\n1043 -174 0 981 54 620 0\n1044 -13 0 1010 633 0\n1045 -346 -136 0 26 634 0\n1046 -138 -48 0 137 636 0\n1047 -302 -289 0 231 638 0\n1048 -119 0 640 243 0\n1049 -168 161 0 981 641 0\n1050 -347 -144 0 137 644 0\n1051 434 436 0 1039 645 0\n1052 -433 131 126 145 140 150 152 147 108 111 0 964 971 952 650 0\n1053 -45 348 0 961 651 0\n1054 -172 -206 0 1010 653 0\n1055 -444 98 99 100 101 103 78 79 82 0 1040 1032 654 0\n1056 -385 121 122 123 0 955 664 0\n1057 -136 -34 0 137 671 0\n1058 -234 227 0 979 672 0\n1059 -412 130 131 125 144 145 139 0 964 971 673 0\n1060 -283 -300 0 640 675 0\n1061 -170 -192 0 1010 678 0\n1062 -96 0 680 98 0\n1063 -177 -194 0 54 684 0\n1064 -279 -313 0 173 685 0\n1065 -349 -8 0 26 687 0\n1066 -24 -141 0 26 690 0\n1067 -60 0 1031 137 702 0\n1068 -433 129 131 126 150 151 152 147 108 109 111 0 964 952 705 0\n1069 -191 -203 0 381 707 0\n1070 -238 -213 0 1038 714 0\n1071 -423 100 101 102 53 54 55 61 62 0 1067 719 0\n1072 -359 2 9 0 963 725 0\n1073 234 0 137 726 0\n1074 227 0 1073 1058 0\n1075 -421 149 156 107 114 0 955 728 0\n1076 -190 -196 0 381 729 0\n1077 -400 156 107 114 0 955 731 0\n1078 -73 0 26 732 0\n1079 -7 0 733 323 0\n1080 -214 -237 0 425 738 0\n1081 -437 31 32 34 38 39 41 45 46 48 14 0 951 963 745 0\n1082 -393 89 90 86 57 0 1000 960 746 0\n1083 -51 0 747 259 0\n1084 -293 -268 0 623 753 0\n1085 -217 -258 0 425 755 0\n1086 -262 -236 0 219 757 0\n1087 -176 -187 0 54 758 0\n1088 -114 -27 0 137 759 0\n1089 -402 53 54 56 79 82 0 960 1040 1032 761 0\n1090 -243 229 0 1074 763 0\n1091 -236 -254 0 544 765 0\n1092 -262 263 0 1073 766 0\n1093 -433 129 130 126 136 137 133 158 159 154 109 110 0 952 769 0\n1094 -159 0 387 771 0\n1095 -433 129 130 125 126 136 137 132 133 158 153 154 0 1094 772 0\n1096 -405 64 76 83 87 89 0 1067 1078 1040 779 0\n1097 -321 -82 0 26 781 0\n1098 -363 61 62 0 1067 786 0\n1099 -335 0 137 961 787 0\n1100 -445 156 157 158 107 108 109 114 115 116 121 122 0 955 796 0\n1101 -151 0 798 492 0\n1102 -117 -91 0 961 799 0\n1103 -381 61 63 82 0 1067 1040 1032 800 0\n1104 -398 45 48 9 14 0 1079 963 801 0\n1105 -433 129 125 126 136 132 133 146 147 158 153 154 0 1101 806 0\n1106 -399 99 100 101 53 54 0 960 809 0\n1107 -357 99 0 960 811 0\n1108 -312 -318 0 798 816 0\n1109 -35 0 820 308 0\n1110 -66 0 821 326 0\n1111 -232 0 821 1022 0\n1112 -239 0 821 1074 589 0\n1113 -72 0 1111 269 0\n1114 -432 0 1111 343 0\n1115 -79 0 1112 368 0\n1116 -414 0 1112 742 0\n1117 -6 0 462 822 0\n1118 -325 -144 326 0 137 825 0\n1119 -8 321 0 1031 137 826 0\n1120 -115 -78 0 961 827 0\n1121 168 0 828 486 0\n1122 -126 0 828 1023 0\n1123 -113 0 828 626 0\n1124 -349 0 828 1065 0\n1125 321 0 828 1119 0\n1126 -181 0 1121 523 80 0\n1127 161 0 1121 1049 0\n1128 -348 0 1124 828 1013 0\n1129 -82 0 1125 1097 0\n1130 -431 0 1126 135 0\n1131 -180 0 1126 981 244 0\n1132 287 0 1126 1111 803 0\n1133 -179 0 1127 462 305 0\n1134 -45 0 1128 1053 0\n1135 433 0 1130 1114 242 0\n1136 -21 0 1131 61 0\n1137 -410 0 1131 239 0\n1138 -274 0 1132 773 235 0\n1139 -407 0 1133 320 0\n1140 9 22 61 114 0 1113 1122 830 0\n1141 -329 -44 0 26 831 0\n1142 129 130 131 125 0 1135 964 1122 832 0\n1143 -388 131 145 150 152 0 964 971 833 0\n1144 -20 0 1133 835 0\n1145 -439 142 149 156 107 114 0 955 839 0\n1146 -368 23 25 36 0 1109 841 0\n1147 -216 -251 0 425 842 0\n1148 -292 -315 0 773 843 0\n1149 -406 116 117 129 130 134 136 137 0 1123 973 844 0\n1150 -207 -172 0 747 846 0\n1151 -129 -33 0 26 848 0\n1152 -291 -308 0 773 851 0\n1153 -22 0 1126 852 0\n1154 231 286 0 1131 853 0\n1155 -14 0 1043 854 0\n1156 -332 -153 0 137 855 0\n1157 -299 -269 0 231 859 0\n1158 -23 0 137 863 0\n1159 -444 99 100 101 103 53 54 56 0 960 1115 1040 1032 1129 864 0\n1160 -111 0 867 94 0\n1161 -243 236 0 1073 868 0\n1162 -334 -98 0 26 1099 869 0\n1163 -254 255 0 979 874 0\n1164 -231 -213 0 544 877 0\n1165 -331 -44 332 0 26 888 0\n1166 -297 -309 0 623 889 0\n1167 187 294 0 1112 890 0\n1168 323 0 961 26 893 0\n1169 324 0 1168 137 828 20 0\n1170 -387 75 76 77 83 84 0 1129 894 0\n1171 -215 -244 0 425 896 0\n1172 -137 -41 0 137 906 0\n1173 -162 -185 0 462 913 0\n1174 -238 231 0 1073 916 0\n1175 -206 -211 0 546 918 0\n1176 -391 136 137 132 158 153 0 1094 922 0\n1177 -298 -316 0 623 924 0\n1178 -97 343 0 961 926 0\n1179 -254 -228 0 680 929 0\n1180 -229 -253 0 821 932 0\n1181 -195 -176 0 820 935 0\n1182 -343 -98 344 0 828 937 0\n1183 -281 0 1132 640 939 0\n1184 129 130 131 108 109 110 0 1135 964 1122 1160 952 940 0\n1185 -248 0 944 1073 384 0\n1186 -247 0 944 1074 395 0\n1187 -88 0 1185 115 0\n1188 -438 0 1185 356 0\n1189 -87 0 1186 70 0\n1190 -417 0 1186 928 0\n1191 129 150 147 157 158 154 108 109 0 1135 964 1122 1101 952 945 0\n1192 -184 -200 0 1131 950 0\n1193 -264 -318 0 387 680 1101 1062 1025 961 828 987 26 1160 1134 1117 1000 1108 657 125 67 127 1009 885 567 555 5 136 1017 63 77 7 1162 389 0\n1194 244 102 27 -154 157 115 133 298 49 0 1115 39 313 372 457 1061 287 519 770 0\n1195 -97 -98 -318 0 387 961 1010 867 1101 1062 1025 828 747 1129 1185 623 1183 1132 1133 462 355 381 944 821 1153 1044 1073 282 1038 340 108 92 558 370 504 978 572 43 1193 527 1021 74 156 125 67 380 885 1178 1037 818 1182 5 1002 417 517 1016 41 1045 876 581 591 423 1076 391 836 727 81 1047 715 807 884 905 311 704 316 117 42 762 866 1154 862 1167 570 177 440 153 907 537 278 69 1164 190 694 34 1150 155 442 101 545 515 421 627 743 1140 850 265 1088 29 1194 40 149 162 271 1171 1080 369 870 647 528 829 1071 0\n1196 -89 0 1169 1125 1129 1014 1020 976 1036 581 0\n1197 -114 10 145 84 133 279 65 83 90 -28 138 152 0 1185 1132 1011 1115 1196 1187 1189 1032 1040 1067 1160 1135 1122 532 73 591 1076 727 1047 316 570 116 1088 938 472 770 87 847 785 481 1007 0\n1198 -75 -61 130 203 312 0 961 355 1137 680 101 69 439 237 121 91 103 274 1027 858 847 93 0\n1199 -102 294 108 83 90 -28 298 157 -318 0 747 1185 1183 961 1025 1062 1101 1083 1033 1000 1117 1134 1160 387 381 1196 1010 1133 1153 355 1129 1040 1078 1067 828 1094 1135 1122 1167 190 515 862 1108 657 125 67 5 142 658 1141 111 1195 389 630 84 908 1064 1034 591 1076 727 807 564 715 711 517 417 247 1069 39 19 41 876 1193 156 777 29 776 850 683 442 123 292 337 1061 295 823 519 611 1197 1140 101 69 1154 1041 207 473 797 1198 124 172 500 541 1019 0\n1200 -236 102 99 98 -423 0 219 984 1086 158 369 647 609 0\n1201 -100 76 -408 83 90 0 544 219 1038 1196 50 647 9 158 271 513 709 313 241 0\n1202 102 99 -408 5 57 83 90 98 291 -423 0 387 1000 1117 1134 1160 1011 282 1196 1189 1040 1078 1067 389 630 1064 532 73 84 908 1034 1200 607 865 1192 899 1201 609 369 756 149 313 565 962 834 892 988 225 0\n1203 75 -366 -381 114 145 118 117 -439 142 144 0 1040 1078 1067 1129 961 1123 172 124 102 917 995 0\n1204 296 298 317 -318 0 1196 1025 1062 1101 747 961 828 1185 1033 1083 944 219 1183 1188 1132 1160 1134 1117 1000 1139 821 387 623 1010 1133 1153 1129 1094 1135 1122 440 177 125 67 5 417 41 876 1193 156 1108 657 921 581 142 992 591 658 247 423 1076 1141 1069 836 153 727 914 111 694 34 196 715 807 721 885 1195 517 421 542 711 42 564 762 1085 389 171 710 537 400 630 895 692 155 84 96 1064 743 908 871 883 1202 29 1199 850 90 311 442 116 473 292 337 295 823 797 611 1203 1198 1140 1103 624 541 1019 0\n1205 -44 -36 0 961 828 987 26 1160 1134 1117 1000 1017 136 77 63 1162 7 389 0\n1206 -55 102 49 138 157 -153 0 528 563 1171 457 313 0\n1207 -192 -422 49 0 1133 1158 1136 1155 1079 1134 233 1061 655 519 568 0\n1208 170 -422 49 0 1121 1158 1136 1155 1079 1134 519 750 568 655 0\n1209 37 298 317 -318 0 1083 1033 1094 1000 1117 1134 1160 1188 798 623 1129 1196 1025 1062 387 1101 944 1185 1186 747 1073 1074 425 820 963 1155 1144 1038 1112 125 67 5 1204 81 727 1076 591 581 824 1057 417 748 712 691 927 358 793 721 22 662 667 39 1108 657 1205 111 1195 389 630 96 440 177 517 52 41 876 1193 156 850 421 708 34 603 604 153 176 665 369 647 85 694 897 1206 1207 372 40 245 676 1171 1080 167 743 350 829 545 298 898 795 899 1208 510 784 689 362 953 802 1172 724 542 112 698 353 488 993 0\n1210 -244 -423 102 98 0 282 1038 1112 149 271 676 369 647 743 609 0\n1211 -100 -30 -37 264 0 1133 442 337 823 647 499 493 873 975 666 611 0\n1212 99 100 83 -423 102 -37 34 145 150 142 138 108 -318 0 355 1000 1117 1134 1011 1025 1062 387 1101 1083 1033 1094 1196 1189 1040 1078 1067 1187 1160 1135 1122 1010 1153 1108 657 125 67 5 1205 111 1195 1210 313 613 389 630 1064 532 73 92 108 1034 1193 1200 607 609 37 369 756 915 193 596 879 347 565 91 1154 252 481 273 1041 559 1052 409 116 106 1140 515 0\n1213 298 317 -318 0 1011 1025 1062 387 1101 1083 1033 1094 1000 1117 1134 1160 623 798 1185 1129 820 219 1111 1196 1189 1040 1078 1067 1108 657 125 67 5 1205 111 1195 389 630 96 871 440 177 1064 532 73 1034 885 1193 39 1204 81 691 22 878 727 667 662 1076 591 581 1057 1209 442 613 717 195 391 836 153 694 196 542 1210 313 457 1211 1212 743 122 224 1006 373 513 834 607 565 0\n1214 -260 84 -263 -318 0 1025 1062 387 1101 1083 1033 1094 1000 1117 1134 1160 1011 944 219 1111 1196 1189 1040 1078 1067 196 542 34 421 1108 657 125 67 5 1205 111 1195 389 630 1064 532 73 1034 885 122 224 1006 373 513 834 607 565 0\n1215 -64 99 -318 0 820 1000 1117 1134 1196 1025 1062 387 1101 1083 1033 1094 960 952 1160 1126 1121 546 1158 1108 657 125 67 5 1205 111 885 1085 943 1195 389 630 84 614 76 895 417 748 310 410 451 481 120 4 580 192 838 55 262 998 455 784 899 246 129 420 465 925 948 519 110 898 364 597 655 450 531 58 0\n1216 102 -423 -318 0 1025 1062 387 1101 1083 1033 1094 1000 1117 1134 1160 1011 944 219 1196 1189 1040 1078 1067 544 665 196 542 34 421 1108 657 125 67 5 1205 111 1195 389 630 1064 532 73 1034 1210 313 1214 743 1200 607 1215 565 513 756 9 609 647 0\n1217 -423 317 -445 0 747 1011 1025 1062 1083 1033 1094 1000 1117 1134 623 1185 1129 944 219 867 1196 1187 1189 1032 1040 1067 961 355 773 1123 387 1160 1101 1122 1135 798 828 6 1213 704 81 727 1076 591 581 1108 657 125 67 5 1205 111 1195 389 630 280 1084 114 1177 760 506 667 1064 3 570 96 871 440 532 73 1034 517 417 41 876 1193 156 665 34 196 421 542 1216 777 717 1214 850 743 662 1215 437 578 87 143 583 101 121 938 69 1154 253 502 412 619 75 165 174 1148 615 413 847 365 1100 805 14 509 1142 1068 299 956 621 402 459 0\n1218 -137 -422 34 -437 -318 0 1196 1025 1062 387 1101 1083 1033 1094 981 820 963 1155 1144 836 195 442 1108 657 125 67 5 1205 111 417 748 191 1172 1208 304 510 784 298 898 689 362 795 899 953 0\n1219 317 -445 0 820 1196 1025 1062 387 1101 1083 1033 1094 623 1185 1188 1129 747 1038 219 1112 6 1108 657 125 67 5 1205 111 885 1085 417 748 712 52 177 1213 506 704 667 927 81 358 793 727 721 1076 591 581 1057 824 1217 694 836 85 897 1218 724 542 112 196 294 1012 698 1090 1161 923 353 686 176 1092 676 309 488 677 238 528 647 369 545 829 993 743 0\n1220 -83 -445 0 820 1196 1025 1062 387 1101 1083 1033 1094 1038 219 1112 1129 1185 1183 798 1132 1219 999 6 1108 657 125 67 5 1205 111 885 1085 517 417 748 712 284 542 112 196 294 1012 698 1090 1161 923 353 686 176 1092 676 309 488 677 238 528 647 369 743 545 829 993 358 927 691 921 581 591 247 1076 1069 727 858 715 807 909 307 711 14 847 805 478 1142 143 188 682 782 583 0\n1221 290 136 -445 0 1083 1033 1094 1196 1025 1062 1101 387 1183 1129 1185 1132 1219 999 581 591 1076 727 909 847 807 14 6 125 715 711 67 5 1108 657 1205 111 517 805 478 1142 143 188 682 782 583 0\n1222 -286 136 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1134 1188 1183 1185 1132 1190 773 1186 523 798 1196 387 680 1187 1160 971 1122 1135 964 1123 828 1129 1040 1078 1067 1189 1133 546 1127 581 992 591 1076 599 1219 366 60 1220 518 446 452 1069 1221 307 858 274 91 328 661 416 364 273 1151 164 286 468 6 125 727 715 42 171 999 909 847 807 14 711 914 721 1047 662 1108 657 67 5 1205 111 1195 389 630 1064 883 84 908 251 1041 871 116 207 958 995 473 221 505 500 317 172 474 797 597 295 118 337 262 618 427 442 362 899 808 0\n1223 136 -445 0 1196 1025 1062 387 1101 1083 1033 1094 1000 1117 1134 1160 1011 1129 1185 1183 1133 821 355 1122 1135 1067 1219 999 662 6 1108 657 125 67 5 1205 111 1195 389 630 1064 532 73 1034 581 591 1076 727 715 807 909 711 762 847 537 155 743 1215 1221 1222 188 1154 543 69 150 101 1024 221 785 223 0\n1224 130 286 131 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1134 1160 1011 1196 387 623 798 1122 1135 1129 1032 1040 1067 381 355 1154 69 101 188 1223 921 81 1219 366 60 1220 518 446 452 1069 999 662 697 6 1108 657 125 67 5 1205 111 1195 389 630 1064 532 73 1034 1142 805 307 543 858 150 749 1024 834 16 221 716 327 223 587 622 990 870 190 930 342 1035 213 230 272 0\n1225 286 131 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1160 1010 355 387 1155 1134 381 1196 1187 1189 1032 1040 1067 1220 1219 366 6 1108 657 125 67 5 1205 111 1195 389 630 1064 92 108 1154 69 879 101 68 1224 711 861 217 198 533 982 1104 627 819 515 1150 1215 190 100 78 1167 817 377 723 0\n1226 61 64 -130 131 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1134 1011 1196 387 1153 1010 1111 960 952 1160 1067 1225 1041 116 6 1108 657 1219 366 60 1220 518 446 1223 554 524 507 999 662 1143 452 1069 125 67 5 1205 111 1195 389 630 1064 532 73 1034 1140 515 205 106 254 559 192 252 2 224 743 120 580 4 549 794 223 0\n1227 9 75 400 48 76 388 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1160 1196 387 623 1188 963 1155 1134 282 1223 921 81 793 721 1057 1219 366 60 1220 518 446 452 1069 612 6 1108 657 125 67 5 1205 111 1195 389 157 1104 35 444 533 1173 68 559 149 252 313 1170 0\n1228 -64 -318 0 834 1215 1006 743 0\n1229 -130 131 -445 0 1025 1062 1101 1083 1033 1094 1196 387 1155 1134 6 1108 657 1219 366 60 1220 518 446 1223 554 524 507 999 662 1143 1228 125 67 5 1205 111 1193 315 711 861 1226 217 88 198 1104 1227 533 91 68 596 0\n1230 -61 131 -445 0 1025 1062 1101 1196 387 623 1188 355 1137 961 1129 1040 1078 1067 546 1010 963 1155 1144 1229 1223 921 81 793 721 1057 1219 366 60 1220 518 446 452 1069 612 999 662 6 125 67 5 1205 1108 101 121 1198 69 1142 439 730 237 1059 150 102 317 978 172 473 797 295 262 292 362 1004 442 899 953 0\n1231 63 131 -445 0 1000 1117 1134 1160 1011 747 1196 1025 1062 387 1101 1083 1033 1094 1153 381 640 1129 1032 1040 1067 355 964 1225 1041 116 1230 1140 515 190 1167 232 615 1035 230 6 1228 1108 657 125 67 5 1205 111 1219 366 60 1220 518 446 1223 554 524 718 452 85 836 999 662 697 1195 389 630 1064 532 73 1034 327 223 313 622 777 133 990 870 1210 342 694 213 8 272 871 930 1157 150 0\n1232 131 -445 0 1025 1062 1101 1083 1033 1094 1000 1117 1134 1160 387 1153 1196 1187 1189 1032 1040 1067 1010 381 1111 1044 680 6 1228 1219 366 60 1220 518 446 1223 554 524 507 452 1069 999 662 1108 657 125 67 5 1205 111 1195 389 630 1064 883 1034 1143 1225 1041 116 1230 1140 78 515 106 190 254 559 1167 362 252 377 2 171 723 224 817 743 100 1150 627 265 436 1231 352 549 51 625 488 0\n1233 61 -445 0 1011 867 1025 1062 387 1101 1083 1033 1094 1000 1117 1160 1153 381 1155 1134 282 1185 1196 1187 1189 1032 1040 1067 1232 154 6 1108 657 125 67 5 1205 111 1195 389 630 1064 847 472 116 226 114 1077 79 1228 1220 1219 366 532 73 1034 1140 78 515 190 1167 377 723 817 100 1150 627 982 533 68 149 603 313 421 87 0\n1234 -445 0 387 1101 1062 1025 1094 1033 1083 1160 1117 1000 1011 867 1155 1134 282 1185 1196 1189 1040 1078 1067 6 125 1108 67 657 5 1205 111 1195 389 1034 630 1064 532 73 1220 1228 1232 79 132 154 847 226 472 114 116 1077 1233 88 1104 533 68 149 603 1086 313 421 607 565 0\n1235 -77 -153 107 -61 0 961 355 1136 101 69 812 121 444 513 208 1080 829 0\n1236 -136 152 -144 332 0 961 1169 828 1094 1033 1083 49 976 128 1118 1165 910 111 0\n1237 -156 318 125 0 387 154 760 217 257 711 805 1142 0\n1238 -144 107 -153 -61 0 961 387 828 1129 546 1188 798 219 1155 1134 1156 1003 938 121 88 67 996 125 994 566 667 1236 581 992 591 670 220 1076 52 914 721 1237 1077 1145 980 359 740 307 1166 697 805 724 1142 542 79 196 1104 1092 533 68 0\n1239 -262 258 -429 77 65 0 282 1185 1189 1040 1078 1067 885 149 603 313 421 216 333 424 353 530 0\n1240 -153 107 -61 0 355 1101 1196 1062 1025 1011 747 1234 680 979 1129 1115 101 69 1174 703 1034 630 735 1235 1238 1064 5 532 417 1205 73 41 557 489 632 127 885 555 475 1239 44 369 255 647 1055 743 0\n1241 -36 97 132 53 99 54 100 101 153 -61 0 961 355 1137 747 1234 101 69 439 237 121 417 1205 41 555 557 475 489 1159 418 815 536 0\n1242 136 158 -391 132 156 153 107 114 0 1129 1188 581 1176 992 591 697 1076 1166 914 359 721 1145 0\n1243 -136 327 -144 97 0 961 1169 828 1094 1033 1083 49 976 128 1118 954 872 111 0\n1244 97 262 107 -61 0 979 1136 961 137 1000 1117 1134 1160 1010 867 1132 381 355 1196 387 101 69 1174 213 1240 389 340 108 92 558 370 949 810 215 230 272 812 121 829 208 27 44 701 545 255 743 647 369 1154 1041 538 760 938 1241 264 67 736 1243 125 1242 270 0\n1245 262 107 -61 0 1000 1117 1160 1010 355 381 1155 1134 1101 828 101 69 1154 1041 1240 389 340 108 92 538 198 1174 904 775 88 68 329 533 45 1104 123 1046 683 1244 643 1178 631 1182 1045 1002 1016 0\n1246 -144 -136 -98 0 828 1045 1016 1002 1182 1178 736 1243 0\n1247 -37 30 138 157 -136 84 0 820 442 717 195 457 391 0\n1248 -41 24 144 369 0 971 1158 25 628 966 560 947 0\n1249 41 2 157 44 -136 84 9 0 623 1188 1144 1044 1117 963 381 921 81 793 721 1057 184 157 1046 903 1247 45 36 0\n1250 -41 144 369 0 546 612 1248 185 364 0\n1251 -198 44 -183 -136 0 623 1188 546 1126 1131 747 963 1144 1155 1134 466 795 297 689 185 612 921 81 793 721 1057 41 688 674 919 362 899 903 953 1081 442 627 744 0\n1252 44 -183 -136 0 961 1169 1196 828 1094 1033 1083 976 49 1251 417 264 128 1118 954 910 111 0\n1253 -44 -136 0 1196 1160 1134 1117 1000 430 1205 264 1246 1236 389 1156 0\n1254 -144 -136 0 961 1169 828 1094 1033 1083 1253 976 49 128 1118 954 910 111 0\n1255 -46 83 -423 102 98 -152 0 1000 1117 1134 1160 1196 1189 657 389 630 1064 642 723 627 819 48 1150 1200 100 607 817 1096 0\n1256 -154 90 41 -153 -136 0 820 798 680 1025 1062 1196 1101 747 1234 1011 828 630 1064 532 73 1034 921 1254 5 417 41 557 489 632 1193 72 440 127 885 691 748 289 53 495 313 1253 461 216 444 778 1249 0\n1257 -37 41 98 -136 0 798 680 1025 1062 1196 1101 747 1234 1000 1117 1134 1160 1011 820 219 1044 821 1111 389 630 1064 532 73 883 1034 921 1254 5 417 41 557 489 632 1193 72 177 1253 127 885 555 691 748 289 53 495 313 442 613 717 195 836 153 694 196 542 1255 1256 265 743 155 224 424 513 216 0\n1258 -260 46 -153 -136 0 820 798 680 1025 1062 1196 1101 747 1234 1011 821 1111 1133 1183 381 944 1155 1134 630 1064 532 73 1034 921 1254 5 417 41 557 489 632 1193 72 440 127 885 691 748 289 53 495 313 155 224 424 537 513 933 1239 216 198 68 329 421 708 533 45 34 982 36 176 1046 457 0\n1259 46 41 98 -136 0 747 1234 680 1025 1062 1196 1101 1000 1117 1134 1160 1044 944 1185 1186 389 630 1064 883 1034 1254 5 1253 417 41 557 489 632 127 885 555 475 1258 743 265 1256 421 34 603 604 176 369 647 404 0\n1260 -90 171 -153 -136 0 1025 1062 1196 1101 747 1234 1121 465 597 420 1254 5 417 41 557 489 632 1193 630 942 64 1253 1252 364 554 119 421 483 1147 700 576 0\n1261 41 98 -136 0 623 747 1234 680 1025 1062 1196 1101 1000 1117 1134 1160 1129 389 630 1064 1254 5 1253 417 41 557 489 632 127 885 555 475 1193 270 876 921 81 1257 1259 627 374 295 1260 850 662 454 279 437 590 473 114 797 1240 1103 0\n1262 98 -136 0 747 1234 680 1025 1062 1101 1160 1134 1117 1000 1196 219 1254 5 1253 417 41 557 489 632 127 885 555 475 389 1261 902 1250 206 792 542 984 1086 196 158 369 176 647 404 743 819 1258 0\n1263 -41 -136 0 820 798 1025 1062 1101 747 1234 680 1196 1111 1262 340 1030 1254 5 417 41 557 489 632 127 885 921 691 927 748 712 358 824 802 902 1250 206 792 542 984 373 1091 238 923 677 488 353 829 528 545 1029 0\n1264 -243 -136 0 820 798 1025 1062 1196 1101 747 1234 680 1038 1112 1262 340 1030 1254 5 417 41 557 489 632 127 885 921 691 927 748 712 358 824 112 1012 698 1090 1161 923 353 309 488 677 238 528 545 829 1029 0\n1265 -94 -136 0 623 1025 1062 1196 1101 680 1187 1254 5 1253 1252 364 921 81 878 1057 309 398 274 273 91 0\n1266 -236 -136 0 820 798 747 1234 1025 1062 1196 1101 355 1010 867 1132 1111 219 381 680 1129 1032 1040 1067 961 1265 1264 542 1262 340 108 92 558 370 114 1030 735 1254 5 1253 417 41 557 489 632 127 885 555 475 921 691 748 289 53 495 313 927 712 358 824 984 373 1086 1091 238 158 677 488 369 1245 353 829 810 647 545 215 230 256 1029 225 435 322 813 240 159 203 272 24 18 102 0\n1267 -91 -391 132 -136 0 820 798 680 1025 1062 1196 1101 747 1234 961 355 1011 173 1123 941 147 570 1263 1262 340 108 713 73 735 74 921 1254 5 417 41 557 489 632 1193 72 440 691 748 289 53 495 313 1253 435 1102 18 150 978 143 163 116 170 1041 23 1249 188 805 882 534 1142 0\n1268 -55 93 389 -136 0 1185 820 798 1025 1062 1196 1101 747 1234 961 355 1011 1129 173 680 1123 623 1067 986 944 1265 1264 542 1262 340 108 713 73 43 74 1254 5 417 41 557 489 632 127 885 921 691 748 289 53 495 313 927 712 358 824 81 727 1076 322 813 159 272 941 147 570 1267 256 104 488 260 51 163 352 116 938 90 716 288 1167 16 629 870 426 660 420 783 382 0\n1269 -391 132 63 116 117 93 -136 0 1185 820 798 1025 1062 1196 1101 747 1234 680 961 355 1011 173 1123 623 1067 986 944 1265 1262 340 108 713 73 43 74 1254 5 417 41 557 489 632 127 885 921 691 927 748 712 358 824 81 727 1076 941 1267 147 570 163 116 938 90 716 288 1167 16 629 870 426 660 420 783 382 0\n1270 -390 93 53 54 -136 0 961 1011 960 1010 867 1132 381 747 1234 680 820 798 1025 1062 1196 1101 1129 355 1123 1067 1000 1254 5 1265 824 921 691 927 417 748 712 358 41 557 489 632 127 885 1262 340 108 92 558 370 463 109 376 579 215 230 1268 1029 260 104 1264 542 713 73 43 74 289 53 495 313 159 213 1120 342 163 870 938 383 0\n1271 93 53 54 -136 0 820 798 1025 1062 1196 1101 747 1234 961 1011 960 355 1010 867 1132 381 680 173 137 1123 1262 340 108 92 558 370 463 109 376 579 215 230 1265 713 73 74 1254 5 417 41 557 489 632 127 885 921 691 927 748 712 358 824 1268 1029 104 488 260 51 352 1270 272 941 1269 147 27 570 1072 163 170 0\n1272 -93 46 -136 0 623 1185 1025 1062 1196 1101 747 1234 961 355 1010 1138 1133 680 1139 640 867 1187 773 1044 828 1189 955 1123 1262 340 108 92 140 619 43 74 1254 5 417 41 557 489 632 127 1253 1252 364 921 81 727 1076 878 1057 33 353 886 509 530 1163 1179 447 537 274 449 692 385 739 91 227 639 502 273 328 265 1151 468 511 474 31 597 46 201 178 113 1051 0\n1273 -18 -53 -136 0 1186 1094 1043 545 338 584 1262 735 1254 300 597 1 324 814 774 0\n1274 -374 10 31 17 18 12 -136 0 1025 1062 1196 1101 747 1234 680 867 1134 820 733 546 1043 1158 1253 1254 5 417 41 557 489 632 127 885 555 657 361 614 1262 340 1030 943 76 920 1252 364 556 774 899 298 548 110 181 1192 531 420 450 925 246 58 0\n1275 68 -129 12 -53 -136 0 747 1234 680 1025 1062 1101 773 1186 1189 828 1196 820 1094 961 1129 805 328 661 1181 655 468 1151 103 1273 1262 340 545 338 214 421 584 1030 400 735 1254 5 1253 417 41 557 489 632 127 885 555 475 474 14 646 17 1060 1082 577 47 767 510 519 1274 814 1 102 815 12 0\n1276 -68 -213 93 -136 0 820 798 1025 1062 1196 1101 747 1234 680 961 355 1011 425 1133 640 828 1135 1122 1123 1164 1154 1041 116 167 537 385 639 1265 1262 340 108 713 73 74 1254 5 417 41 557 489 632 127 885 921 691 927 748 712 358 824 449 500 1179 194 225 256 104 490 260 985 163 434 0\n1277 -53 46 -136 0 623 820 798 961 1025 1062 1196 1101 747 1234 1011 355 1010 867 1132 979 425 1133 640 1183 1044 1187 680 1123 173 1272 1265 1262 340 108 92 558 370 114 713 73 1253 1254 5 417 41 557 489 632 127 885 555 657 361 1030 679 43 74 921 691 927 748 712 358 824 1252 364 81 878 1057 545 15 167 1070 1164 537 1154 385 933 1041 639 760 116 265 357 1276 1275 273 91 840 274 1075 764 258 911 225 592 256 1069 104 260 880 163 659 570 147 0\n1278 -91 -54 -136 0 961 355 1011 1185 1137 820 798 680 1025 1062 1196 1101 747 1234 381 282 173 1123 829 187 1263 1254 5 417 41 557 489 632 921 691 748 289 53 495 313 1253 1193 72 440 479 1249 515 190 1035 659 147 570 1266 607 1080 513 605 1264 542 703 849 318 1262 340 214 421 857 237 170 346 108 713 73 735 74 667 435 1102 997 163 150 143 978 0\n1279 46 -136 0 820 798 680 1025 1062 1196 1101 747 1234 961 355 1011 282 381 173 1123 1265 1263 1262 340 108 713 73 74 921 1254 5 417 41 557 489 632 1193 72 440 127 885 691 748 289 53 495 313 927 712 358 824 1253 1272 1277 1271 479 829 1249 187 170 515 190 1035 659 147 570 1278 256 104 260 163 0\n1280 -92 93 -136 0 1121 1025 1062 1101 747 1234 680 1189 1196 1138 828 1183 523 1266 607 1264 542 1253 1254 5 417 41 557 489 632 127 885 555 1279 48 1096 627 1150 100 817 723 526 402 470 290 925 1265 1263 488 314 1180 709 263 459 339 956 618 359 480 65 246 0\n1281 93 -136 0 820 798 747 1234 1025 1062 1196 1101 680 979 1129 1115 1113 1110 1279 819 1265 1254 5 1253 417 41 557 489 632 127 885 555 475 921 691 927 748 712 358 824 1280 256 225 1278 240 1271 203 545 15 1276 212 965 91 0\n1282 -136 0 623 798 1101 1062 1025 1234 680 867 1121 747 1196 640 1135 1122 971 964 921 81 691 878 667 1253 1254 5 417 41 557 489 632 127 1193 885 72 555 440 657 361 1264 542 1266 607 1279 390 627 374 470 465 290 360 1281 28 353 886 229 1179 601 312 752 1005 1060 296 697 16 754 585 957 871 0\n1283 28 0 1282 1129 581 0\n1284 -142 0 1283 992 0\n1285 190 0 1283 591 0\n1286 -204 0 1285 546 220 0\n1287 -196 0 1285 1076 0\n1288 -42 0 1286 52 0\n1289 -440 0 1286 712 0\n1290 -34 0 1287 599 0\n1291 302 0 1287 1185 727 0\n1292 -437 0 1287 914 0\n1293 -296 0 1291 623 81 0\n1294 -289 0 1291 1047 0\n1295 300 0 1291 1132 741 0\n1296 -283 0 1291 1183 807 0\n1297 439 0 1292 1188 721 0\n1298 -276 0 1294 1132 316 0\n1299 -122 0 1296 14 0\n1300 -367 0 1296 564 0\n1301 -364 0 1298 179 0\n1302 -115 0 1298 570 0\n1303 -121 44 -93 0 1300 1043 1133 1121 1296 546 1127 231 1190 353 1179 312 118 427 899 455 362 1063 689 337 442 324 795 666 611 900 267 615 1028 13 438 164 808 286 0\n1304 -409 121 356 123 0 1299 955 640 828 710 31 385 511 790 1107 648 0\n1305 -97 -93 0 1038 680 1234 747 1186 1196 773 1299 1189 1284 1290 1187 353 1163 274 91 112 542 28 1091 607 229 1179 449 886 573 885 1303 127 1056 632 601 489 360 557 290 41 875 417 661 901 264 328 934 805 474 273 1066 0\n1306 121 -93 0 1038 680 1133 1121 1139 747 1186 1196 773 1299 1189 1284 1290 1187 1305 353 1163 274 91 112 542 28 1091 607 229 1179 449 886 1056 601 360 139 290 699 470 555 669 657 1304 1108 692 447 574 261 41 875 417 661 901 264 328 934 805 474 273 1066 0\n1307 -93 0 1300 1196 353 1179 666 611 1306 267 1303 1028 1205 934 264 0\n1308 -18 36 -416 0 1043 1133 438 597 324 337 1063 795 442 689 484 0\n1309 -68 148 -44 294 123 0 1196 1133 1307 219 828 640 1144 1160 1135 1122 699 139 925 1205 264 430 862 500 668 459 494 621 709 985 158 639 461 647 385 351 547 39 482 989 476 1007 0\n1310 -314 10 94 18 -144 172 97 -121 0 231 1186 523 1283 1289 387 1307 680 1158 67 994 927 358 125 670 615 13 661 416 364 267 105 183 907 473 988 225 256 488 931 51 160 737 797 0\n1311 285 -44 -121 123 0 1234 1286 1189 1299 1196 640 1190 1158 231 1186 523 1300 1129 680 1133 1139 821 425 381 1132 1185 1307 828 963 1048 615 13 661 416 364 267 164 286 1205 1308 458 611 232 264 67 550 402 1309 124 91 274 764 309 496 468 474 1151 666 1179 695 65 887 994 289 699 1175 557 489 632 127 693 139 925 1054 573 1167 190 515 710 537 722 692 155 167 372 743 545 45 1061 768 903 519 1310 639 656 198 760 329 533 603 1086 421 607 792 1161 947 542 1026 1201 956 319 740 459 1106 621 479 881 166 970 911 0\n1312 147 -363 154 129 318 133 0 1101 1283 798 1293 961 1282 1122 1135 270 1001 985 583 785 148 635 942 1098 419 551 630 121 1105 0\n1313 -147 -44 -121 123 0 1133 1283 1289 1189 1299 1196 640 1190 1158 231 1186 523 1300 1129 680 828 798 1307 1282 615 13 661 416 364 267 164 286 1205 1308 458 611 232 264 67 550 402 1309 124 91 274 309 468 474 1151 994 927 358 670 699 1054 100 139 925 573 46 397 490 754 621 256 637 336 459 225 143 697 956 988 1149 330 817 0\n1314 -44 -121 123 0 231 1190 1116 1286 1196 387 1299 1189 640 1101 1282 1135 1122 1301 1158 733 1134 1083 615 232 606 306 13 164 286 862 468 267 699 1205 1054 663 264 67 125 550 270 402 1308 1309 474 1151 1311 385 639 1313 1001 985 1312 408 505 234 144 332 250 540 411 393 860 627 897 497 0\n1315 318 129 147 154 44 -413 133 17 0 1101 1282 1135 1122 1301 1158 733 981 1286 1285 985 505 270 1312 1001 234 408 144 332 250 304 1061 784 393 860 898 36 912 362 899 199 442 0\n1316 -318 0 387 1101 1196 1062 1025 1234 747 125 1193 67 632 5 489 417 557 41 0\n1317 -158 0 1316 270 0\n1318 147 154 44 -413 -416 133 141 17 0 1135 1122 1316 828 1299 1189 546 1043 1133 1121 1127 985 1315 505 500 1151 474 597 118 324 337 618 455 427 795 442 362 899 808 0\n1319 -290 277 0 798 1316 1297 1284 867 1132 1010 1160 1134 1117 1000 355 307 257 23 359 760 116 1145 114 226 508 572 630 92 389 108 340 0\n1320 -130 396 69 39 44 123 0 1307 1043 956 711 1152 402 804 459 431 925 936 181 899 0\n1321 -270 130 290 137 154 133 0 1293 1316 1317 1282 1122 1135 805 635 942 782 551 630 188 1095 0\n1322 154 -121 123 0 1190 231 1186 523 640 1116 828 798 680 1094 1317 1282 1122 1135 387 867 1160 1134 1117 1000 1010 355 1314 615 232 606 306 13 661 416 164 286 862 468 267 1318 236 754 621 637 336 697 1319 805 227 274 1163 845 1320 1321 583 1093 908 84 361 630 593 389 92 340 108 0\n1323 224 137 130 69 129 -408 138 116 124 117 70 118 134 0 1010 1138 1011 1282 973 1123 1144 979 219 1038 1186 1196 92 713 140 73 619 56 132 989 482 647 44 158 271 604 1086 1090 313 421 607 542 241 0\n1324 137 130 69 109 129 -408 138 116 124 117 70 118 9 133 134 0 355 1134 1117 1000 387 1160 1282 1122 1135 867 1153 1323 108 340 389 630 84 1064 908 991 847 226 472 114 116 1240 1140 0\n1325 -297 109 254 129 124 298 70 44 -282 0 640 387 1094 1033 1083 1160 1101 1282 1122 1135 1144 39 232 862 366 285 336 165 657 754 619 111 974 885 989 686 482 647 0\n1326 69 109 39 -121 123 0 381 387 1139 231 1186 523 680 1316 640 828 615 1314 1322 461 232 639 351 385 547 183 1319 805 13 661 416 227 274 1163 1325 697 845 710 692 39 143 105 171 586 1167 190 515 862 46 1320 1324 0\n1327 -131 100 -154 0 828 640 1144 639 385 547 461 989 847 482 1148 619 0\n1328 109 39 -121 123 0 640 1316 231 1186 523 680 828 219 1101 867 1144 1160 1282 1122 1135 615 13 661 416 1322 639 183 1319 227 274 1163 805 232 351 39 385 547 461 1314 862 1325 697 1326 621 709 158 647 1327 974 657 525 361 482 908 619 991 1148 711 303 0\n1329 -270 0 867 1316 1295 1010 1160 1134 1117 1000 355 578 942 467 630 92 389 108 340 0\n1330 -403 0 1329 64 0\n1331 -109 0 1329 583 0\n1332 -121 123 0 828 387 640 1316 546 381 1121 1296 1299 219 1101 867 1160 1331 1282 1122 1135 1153 615 1314 1322 1328 232 639 461 236 362 862 1167 105 385 183 351 262 998 190 547 1319 39 465 360 515 805 312 1179 1325 697 1018 601 275 158 647 1327 974 657 361 908 991 711 837 582 1140 116 0\n1333 271 133 138 137 131 -314 0 1316 1160 1331 1282 1122 1135 387 1297 1284 183 1319 805 105 908 991 711 740 217 32 582 760 114 116 1145 0\n1334 -271 138 131 -154 124 0 1316 387 867 1160 1134 1117 1000 1101 1299 1282 1011 355 639 183 1319 805 143 586 84 361 630 657 389 86 340 73 108 713 0\n1335 138 137 131 -154 124 0 623 1153 961 1316 1297 1284 639 183 1319 805 1334 1333 1015 862 90 116 1140 121 1237 1142 711 740 32 1145 114 0\n1336 -298 131 -154 0 1316 867 1302 1123 1011 355 1160 1134 1117 1000 387 1331 1297 1284 639 183 1319 805 143 105 171 586 791 1177 871 760 652 116 163 73 713 108 340 389 630 84 508 908 114 1184 1145 740 0\n1337 131 -154 124 0 1316 1331 387 1297 1284 639 183 1319 805 105 1336 39 1334 1335 908 697 1166 585 359 871 1184 711 217 32 582 760 114 116 1145 0\n1338 -100 -408 0 979 219 1186 647 44 158 604 1086 1090 421 607 542 1201 0\n1339 -154 100 124 0 1337 1327 0\n1340 -131 70 100 124 0 1144 989 847 482 1148 619 0\n1341 83 76 -153 -384 154 0 387 1196 828 1126 1286 1301 1283 1135 1122 630 84 275 1180 681 229 206 621 1042 580 192 55 784 887 144 947 234 539 32 114 1240 1098 521 785 985 0\n1342 -36 263 98 -408 0 821 747 1316 1234 680 1092 369 176 1338 447 155 743 417 1205 41 557 261 489 127 404 885 475 555 0\n1343 -83 54 98 92 -408 0 821 425 219 1196 1289 1307 1283 680 944 1298 1331 733 1285 1338 447 167 545 155 743 284 542 196 1012 176 1092 309 369 1342 264 67 994 927 358 946 993 225 283 528 734 240 988 321 203 209 318 38 134 250 795 422 0\n1344 -144 102 101 94 130 98 214 131 92 100 53 99 0 1000 1117 1134 1160 387 1289 1307 1283 680 944 1331 1329 1287 389 630 84 908 829 67 670 994 927 358 946 993 225 283 528 734 780 240 321 1184 203 318 805 134 97 795 810 891 0\n1345 102 101 99 94 130 98 214 131 92 100 53 0 680 1234 1316 747 1025 1062 1196 1101 1344 5 417 1205 41 557 261 489 127 404 885 475 555 0\n1346 144 78 354 145 101 98 -408 0 821 1101 1196 1062 1025 747 1234 1129 1115 1338 447 155 743 5 11 417 1205 180 41 146 557 487 489 1055 0\n1347 -315 131 -384 154 -408 0 425 821 1126 1138 1010 355 1160 1134 1117 1000 1283 944 828 462 1129 1115 1330 275 1180 488 447 155 535 977 648 669 334 1338 167 545 743 140 1148 92 66 108 1080 340 829 389 1003 1343 1341 315 415 607 1086 369 1345 176 29 34 151 789 703 1346 71 996 566 210 180 107 266 278 498 617 1089 700 0\n1348 -102 101 98 131 386 -408 0 425 1000 1117 1134 1160 1010 355 1283 944 828 462 1129 1115 1330 389 630 1064 92 108 1003 447 167 545 176 29 34 151 789 703 1346 67 71 996 994 566 667 1143 210 252 180 2 107 266 1080 278 498 829 617 1089 700 0\n1349 -305 150 423 -313 131 124 123 0 425 1307 1067 955 1299 1139 387 1317 1331 1286 828 84 908 1064 1332 31 692 1338 1339 447 167 545 204 999 437 177 440 96 1319 694 871 805 836 1191 1184 663 236 621 1320 699 0\n1350 214 101 98 131 -384 154 -408 0 425 1000 1117 1134 1160 821 1126 447 155 535 977 648 669 334 559 1348 389 275 1180 488 1338 167 545 743 829 1343 1341 315 415 1345 0\n1351 101 98 131 124 123 0 1126 955 1139 821 1121 747 1299 1000 1117 1134 1160 867 1291 1153 1331 1317 1101 1282 1135 1122 389 630 1064 1332 1056 31 692 447 155 535 1338 1339 977 648 669 470 290 360 601 334 559 743 1348 609 1350 1080 66 226 909 472 114 437 1349 116 1240 1319 407 1140 805 1341 1015 394 1001 0\n1352 98 131 124 123 0 955 1139 821 1121 747 1299 1160 1134 1117 1000 1332 1056 31 692 447 155 535 1338 1339 977 648 669 470 290 360 601 389 1351 369 1086 607 1161 1341 542 0\n1353 -97 -98 0 680 1316 747 828 1283 1196 885 1178 127 1182 261 1002 41 1016 417 967 264 1050 0\n1354 -258 -425 110 5 69 -144 -259 131 -207 123 0 1121 747 355 680 1329 173 1138 1307 523 546 1300 1129 1331 71 1030 400 108 470 290 925 1150 575 127 818 527 907 866 161 526 110 419 402 899 892 459 956 618 668 65 118 246 823 59 611 363 124 1184 103 0\n1355 -129 37 31 36 107 154 0 773 1316 798 1190 1048 1297 1284 805 1151 307 328 257 1319 359 164 760 637 286 754 484 969 505 0\n1356 -277 129 154 0 798 1293 1331 1317 1101 1282 1135 1122 637 311 754 862 1001 0\n1357 147 129 150 -279 154 0 867 1298 1331 1317 1101 1282 1135 1122 10 440 558 1191 1001 871 862 130 0\n1358 129 69 44 150 131 124 123 0 425 1307 1067 955 1139 821 1134 1010 355 1011 1299 1302 1352 340 108 713 73 92 1332 31 692 447 155 535 1338 1339 977 648 145 448 167 545 204 1356 143 1357 236 397 1320 1008 0\n1359 -211 -144 70 124 123 0 1134 821 1121 1144 355 1010 1132 955 1299 1139 1286 747 1094 1033 1083 867 798 1316 1297 1284 67 994 289 667 71 1332 31 692 1338 1340 1352 1353 340 108 92 558 370 114 1030 943 1339 1056 447 155 535 977 648 669 470 290 360 601 1347 619 482 145 41 1175 699 111 657 525 920 361 614 908 679 76 856 795 1354 693 313 1358 805 1355 307 257 613 359 760 95 1145 751 0\n1360 -144 70 124 123 0 821 1134 1298 355 1010 867 1132 955 1299 1139 1283 1286 680 1285 1316 944 219 1297 1284 1288 1332 31 692 1338 1340 1352 1353 340 108 92 558 370 114 10 447 155 535 1339 977 648 145 67 670 994 667 289 53 1359 423 261 153 495 34 196 313 421 542 95 341 751 1145 980 359 724 1166 697 0\n1361 70 124 123 0 1134 955 1139 821 1121 1299 1144 355 1010 867 1132 1101 1062 1025 747 1094 1033 1083 1285 1298 944 219 1196 1297 1284 1332 1056 31 692 447 155 535 1338 1339 977 648 669 470 290 360 601 1150 145 1340 1347 619 482 1352 340 108 92 558 10 370 114 1353 1360 5 417 1205 41 247 111 423 411 525 153 38 34 196 162 421 542 313 95 229 341 751 514 1145 0\n1362 156 149 -363 144 123 154 107 0 747 1316 680 1083 1033 1025 1062 1196 1101 867 1048 1094 1297 1284 1283 5 1205 417 41 261 127 885 111 657 361 908 968 1145 785 938 1098 0\n1363 -156 110 0 387 1316 1294 1331 154 760 1237 217 257 188 711 805 251 1184 871 0\n1364 144 123 -70 107 0 821 1121 1101 1196 1062 1025 747 1285 1316 680 1300 1301 1033 1083 867 1048 1297 1094 1284 828 1129 424 155 535 461 977 648 669 470 290 1150 5 417 1205 41 247 386 261 411 823 127 144 611 885 234 111 657 361 908 1363 968 1362 500 840 124 0\n1365 -133 61 0 1153 623 1015 862 1140 90 116 0\n1366 -110 -149 -144 0 1283 1289 1112 1307 387 1160 1134 1117 1000 71 980 349 359 1166 60 446 276 698 488 649 67 994 927 358 670 696 908 256 84 1353 630 389 0\n1367 -149 -144 107 0 798 1158 219 1074 1331 1094 1317 1282 1122 1135 640 71 980 359 740 788 349 307 1166 1146 805 60 697 1026 446 947 276 792 196 1086 706 1245 647 1365 1366 1093 639 1339 385 547 0\n1368 -154 123 0 828 640 639 461 385 1361 547 0\n1369 129 110 19 133 294 123 0 1101 828 1331 1094 1317 1282 1122 1135 1307 1368 1001 754 621 336 697 1093 956 711 459 1152 402 0\n1370 -129 156 -144 154 107 0 798 773 1190 1048 1297 1284 828 1299 1189 1367 1145 116 71 805 1151 307 328 348 164 468 754 286 969 1308 500 474 0\n1371 -124 -144 123 107 0 828 1183 1297 1284 1121 747 623 1331 1317 1101 1282 1135 1122 387 867 1160 1134 1117 1000 1010 355 1367 1368 977 511 547 1107 933 648 760 669 1145 470 116 938 290 90 1365 925 1370 1001 1369 754 908 84 361 630 593 389 92 340 108 0\n1372 -110 0 387 867 1160 1134 1117 1000 1094 1033 1083 908 84 361 630 657 389 1353 720 111 0\n1373 -156 0 1372 1363 0\n1374 -144 123 107 0 821 1121 747 1297 1284 1373 623 1372 1368 977 1367 1371 1361 424 155 535 648 669 470 290 925 1145 1370 116 938 90 1365 1369 0\n1375 123 107 0 1048 1372 1297 1094 1284 1101 1196 1062 1025 747 828 1285 1121 1301 1300 1373 1129 1368 977 1374 968 5 1364 500 417 1361 41 511 423 1107 648 669 470 540 141 144 823 234 611 1362 124 840 0\n1376 154 107 0 640 1116 1183 1284 1297 623 1331 1317 1282 1135 1122 1373 773 1101 1196 1062 1025 1190 1375 413 339 359 1145 116 90 1167 1087 655 606 306 938 1365 296 754 1001 805 1370 328 5 164 468 1205 286 1318 0\n1377 -154 0 640 1139 639 385 547 710 1339 692 1338 0\n1378 107 0 1377 1376 0\n1379 268 0 1378 114 0\n1380 -125 0 1378 453 0\n1381 -290 0 1379 1329 97 0\n1382 -292 0 1379 867 226 0\n1383 -129 0 1381 805 0\n1384 -279 0 1382 1132 572 0\n1385 -131 0 1382 847 0\n1386 224 0 1384 1010 92 0\n1387 130 0 1385 1380 1383 1142 0\n1388 -259 0 1386 355 108 0\n1389 291 0 1387 711 0\n1390 -98 0 1388 340 0\n1391 -316 0 1389 387 217 0\n1392 153 0 1390 1000 1117 1134 1160 389 0\n1393 -313 0 1391 1379 508 0\n1394 0 1392 1393 630 0\n"

theorem raw_n8_b7_p0011 (word:Fin 8→Fin 3) (base val:Sat.Valuation)
 (h:ModuleOPG1808CNF.LexModel word (lexRot 8) lexPerm base)
 (heq:∀ i,i<OPG1808Cuts.selectorBase 8→(val i↔base i))
 (hc:OPG1808Cuts.CutModel (n:=8) 7 val)
 (hp:word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(1:Fin 3)∧True):False:=by
 have m:=h.toModel
 have bad:=cert_n8_b7_p0011 (val 1) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 28) (val 29) (val 30) (val 32) (val 33) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 81) (val 83) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 145) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 247) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 267) (val 268) (val 269) (val 270) (val 271) (val 273) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 337) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 355) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 475) (val 476) (val 477) (val 489) (val 490) (val 491) (val 492) (val 493) (val 552) (val 553) (val 566) (val 567) (val 568) (val 587) (val 588) (val 589) (val 594) (val 595) (val 596) (val 608) (val 609) (val 615) (val 616) (val 643) (val 644) (val 645) (val 646) (val 647) (val 678) (val 679) (val 725) (val 726) (val 727) (val 728) (val 729) (val 730) (val 734) (val 735) (val 736) (val 737) (val 738) (val 739) (val 740) (val 741) (val 742) (val 743) (val 744) (val 745) (val 746) (val 747) (val 748) (val 749) (val 750) (val 751) (val 752) (val 753) (val 754) (val 755) (val 756) (val 757) (val 764) (val 765) (val 766) (val 767) (val 768) (val 769) (val 770) (val 771) (val 772) (val 773) (val 774) (val 775) (val 776) (val 777) (val 778) (val 779) (val 780) (val 781) (val 782) (val 783) (val 784) (val 785) (val 786) (val 787) (val 788) (val 789) (val 790) (val 791) (val 792) (val 793) (val 794) (val 795) (val 796) (val 797) (val 798) (val 799) (val 800) (val 801) (val 802) (val 803) (val 804) (val 805) (val 806) (val 807) (val 808) (val 809) (val 810) (val 811) (val 812) (val 813) (val 814) (val 818) (val 819) (val 820) (val 821) (val 822) (val 823) (val 824) (val 825) (val 826) (val 827) (val 828) (val 829) (val 830) (val 831) (val 832)
 exact (Or.elim bad
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 1 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 5) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 15 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 3 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 1 2 (hp.2.2.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 1 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 2 (by decide) 5) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 26 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 0 2 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 17) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 3 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 1) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 0) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 3 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 26 1 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 3 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 6 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 26 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 3 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 30 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 1 3 (hp.2.2.2.1)) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 24 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 7 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 1 1 1 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 0) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 2) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 0 (by decide) 5) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 6 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 3 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 22) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 6) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 3 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 2 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 4) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 3) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 0 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 21) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 1) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 15 1 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 3) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 4 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 0) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 2 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 1) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 0) (by decide)) (b))
 (fun b=>(hc.reach_clause 4 (by decide) 5 1) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 30 2 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 17) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 33 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 3) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 6) (by decide)) (b))
 (fun b=>(hc.reach_clause 4 (by decide) 1 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 6) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 32 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 6 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 1 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 0 (by decide) 4 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 7) (by decide)) (b))
 (fun b=>(hc.reach_clause 1 (by decide) 0 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 42 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 15 2 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 1 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 2 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 7) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 29 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 0 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 26) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 4 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 13 2 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 33 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 2) (by decide)) (b))
 (fun b=>(hc.cut_clause 0 (by decide) 4 0 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 1 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 2 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 2) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 5) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 13 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 1 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 13 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 33 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 6) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 7 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 3) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 37 3 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 1) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 37 4 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 0 (by decide) 7) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 22) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 42 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 4) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 24 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.ambient_clause 4 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 5) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 42 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 1) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 6 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 6) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 0) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 13 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 2 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 0) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 0 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 0) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 15 4 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 1 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 6) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 25) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 6) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 2) (by decide)) (b))
 (fun b=>(hc.reach_clause 1 (by decide) 5 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 13 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 29 2 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 0 (by decide) 5 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 0 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 1 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 1 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 1) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 1 (by decide) 2 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 15 2 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 13 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 1 (hp.2.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 24 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 1) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 1) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 26 2 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 6 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 0) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 17) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 3 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 7) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 1 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 4) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 15 3 2 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 2 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 26 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 15 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 15 3 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 37 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 3 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 4) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))))
end OPG1808CutCertificates
end

end Cut8Prefix0011CompactV3Packet

open OPG1808

theorem solution
    (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin 8, D i (finRotate 8 i))
    (hminimal : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex (fun i ↦ color i (finRotate 8 i)) ≤
        toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r)))))
    (hprefix0 : color (0:Fin 8) (finRotate 8 (0:Fin 8)) = (0:Fin 3))
    (hprefix1 : color (1:Fin 8) (finRotate 8 (1:Fin 8)) = (0:Fin 3))
    (hprefix2 : color (2:Fin 8) (finRotate 8 (2:Fin 8)) = (1:Fin 3))
    (hprefix3 : color (3:Fin 8) (finRotate 8 (3:Fin 8)) = (1:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  exact Cut8Prefix0011CompactV3Packet.OPG1808PhysicalPrefix.predecessor_reachable_of_cut_exclusion
    (fun word ↦ word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(1:Fin 3)∧True) Cut8Prefix0011CompactV3Packet.OPG1808CutCertificates.raw_n8_b7_p0011
    D color htournament hnoRainbow hcycle hminimal ⟨hprefix0,hprefix1,hprefix2,hprefix3,True.intro⟩
