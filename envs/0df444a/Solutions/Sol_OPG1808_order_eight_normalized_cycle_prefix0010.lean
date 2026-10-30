-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix0010
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:05:51.344143+00:00
-- url     : https://prove2.me/submissions/4c07b91e-158c-4fdb-b868-ed009b76075c

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

namespace Cut8Prefix0010CompactV3Packet

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
lrat_proof cert_n8_b7_p0010
 "p cnf 454 1102\n211 264 319 0\n-266 -245 267 0\n-396 240 0\n-273 -305 270 0\n-18 -143 0\n204 256 311 0\n-447 89 90 96 97 103 104 54 55 61 62 0\n-385 154 149 114 108 0\n37 44 92 99 146 153 0\n-454 322 0\n-336 -68 -155 337 0\n-316 -317 310 0\n-359 203 0\n-294 -310 289 0\n-240 -264 236 0\n-417 70 71 72 77 78 79 84 85 86 0\n-282 -321 279 0\n-126 -150 0\n-305 -285 307 0\n-125 286 0\n-216 -229 217 0\n-142 304 0\n-400 135 141 148 155 0\n-227 -266 224 0\n196 248 303 0\n-447 92 93 87 88 89 90 0\n-379 302 0\n-445 139 140 137 146 147 143 113 114 109 120 121 116 0\n1 53 108 0\n-300 -309 302 0\n-23 -30 0\n-42 -133 0\n68 0\n-442 131 132 133 128 129 159 160 161 155 156 0\n-438 61 63 64 65 66 75 76 77 78 79 0\n-71 -96 0\n-15 177 0\n-418 123 124 125 126 127 0\n-271 -294 274 0\n-254 -266 252 0\n-2 164 0\n-33 195 0\n-104 -134 0\n172 224 279 0\n-280 -308 281 0\n-140 302 0\n-214 -201 215 0\n-279 -298 277 0\n-92 -45 -160 0\n-358 309 0\n-290 -281 294 0\n-66 227 0\n-264 -229 265 0\n-438 61 64 65 66 75 77 78 79 82 84 85 86 0\n-442 131 132 134 128 129 152 153 154 148 149 0\n-195 -212 192 0\n401 402 403 0\n-65 -154 -47 0\n-350 16 17 0\n-396 76 77 78 79 0\n-72 -103 0\n-43 207 0\n-259 -245 260 0\n-330 -68 -100 0\n-110 -25 -94 0\n-177 0\n-187 -204 183 0\n-382 146 147 141 0\n-108 -108 0\n-77 -90 0\n-360 255 0\n-193 -198 191 0\n-434 5 12 19 25 32 37 0\n-263 -225 267 0\n-53 -23 0\n-171 -186 173 0\n-21 182 0\n-397 131 132 133 134 0\n-35 -119 0\n-335 -8 -45 336 0\n-412 273 0\n-267 -249 263 0\n-187 -205 184 0\n-442 131 134 128 129 145 147 141 142 152 154 148 149 0\n188 240 295 0\n-146 308 0\n-408 265 0\n-223 -234 222 0\n-89 250 0\n-37 -146 0\n-321 -300 322 0\n-300 -304 297 0\n437 438 439 0\n-357 93 100 0\n-1 -121 -101 0\n-87 -112 0\n434 435 436 0\n-312 -288 316 0\n-240 -262 234 0\n-238 -249 235 0\n-331 -8 -45 332 0\n-49 -134 0\n-183 -170 184 0\n-300 -306 299 0\n-59 221 0\n-145 307 0\n-317 -274 323 0\n-213 -194 215 0\n-439 119 121 125 127 132 134 138 140 153 154 0\n-9 -62 0\n-273 -308 274 0\n-322 -303 317 0\n-112 -38 -101 0\n-297 -278 299 0\n-210 -171 212 0\n-246 -255 241 0\n-77 238 0\n-322 -305 319 0\n175 227 282 0\n-239 -255 234 0\n-313 -295 316 0\n359 360 361 0\n-114 275 0\n-417 72 79 86 93 100 0\n-317 -272 321 0\n-438 64 66 70 72 77 79 84 86 99 100 0\n-238 -248 234 0\n-271 -293 273 0\n-99 260 0\n-68 -123 0\n-413 174 0\n-62 223 0\n-1 -64 -141 0\n-77 -132 0\n-95 -120 0\n-382 303 0\n-318 -281 323 0\n-171 -188 175 0\n-356 202 0\n350 351 352 0\n-227 -262 222 0\n-353 186 0\n-366 53 54 55 0\n-203 -166 208 0\n-1 -92 339 0\n45 52 100 107 154 161 0\n-4 -147 -101 0\n-308 -316 309 0\n-246 -257 243 0\n-443 191 0\n-110 271 0\n-117 278 0\n-295 -321 292 0\n-23 -140 -104 0\n-4 -93 -155 0\n-384 95 102 53 0\n-1 -23 327 0\n-1 -62 -128 0\n-219 -251 217 0\n-261 -263 256 0\n-328 -68 -37 0\n-377 195 0\n-309 -318 304 0\n-426 89 96 103 54 61 0\n-372 70 77 84 0\n-408 103 104 54 55 61 62 0\n-388 319 0\n-375 76 77 78 0\n-322 -308 323 0\n-70 -89 0\n-68 -133 -41 0\n-165 -195 168 0\n-261 -267 260 0\n-186 -201 187 0\n-272 -297 269 0\n-442 131 129 145 142 152 149 159 156 111 108 0\n-79 -134 0\n-403 146 142 161 156 113 108 0\n-111 -135 0\n-357 92 93 0\n4 34 57 87 112 141 0\n-440 183 0\n-404 39 40 41 46 47 48 0\n-1 -37 335 0\n23 0\n-120 -100 -47 0\n-442 131 133 134 129 145 146 147 142 111 113 114 108 0\n-2 -73 0\n-180 -209 181 0\n-282 -319 277 0\n-190 -170 191 0\n-348 223 0\n-442 134 128 129 140 135 136 147 141 142 154 148 149 0\n-253 -256 249 0\n-119 280 0\n-442 131 132 133 129 159 160 161 156 111 112 113 108 0\n-368 172 0\n-362 46 47 0\n-314 -298 312 0\n-356 38 45 0\n-410 2 4 9 11 16 18 30 31 0\n-63 -81 0\n-310 -273 315 0\n-247 -265 244 0\n-141 303 0\n213 266 321 0\n-134 -158 0\n-233 -263 228 0\n-106 267 0\n-55 -23 -135 0\n-264 -232 268 0\n-400 140 135 147 141 154 148 0\n-281 -310 276 0\n-224 -247 227 0\n-439 116 117 118 119 120 121 0\n-427 305 0\n-428 42 49 2 9 16 0\n-216 -233 221 0\n-44 208 0\n-9 -117 0\n-120 281 0\n-295 -317 289 0\n-390 61 64 75 77 82 84 0\n-276 0\n-132 -144 0\n-319 -287 323 0\n-412 108 109 110 111 112 0\n-1 -65 -148 0\n-105 266 0\n-433 321 0\n-193 -197 190 0\n-445 137 143 150 157 109 116 0\n-370 279 0\n-417 69 72 76 79 91 93 98 100 0\n356 357 358 0\n-180 -203 176 0\n-444 243 0\n-445 138 139 140 135 136 137 0\n-318 -280 322 0\n-139 -152 0\n-206 -186 208 0\n-209 -212 206 0\n-16 -68 0\n-241 -217 244 0\n-280 -305 277 0\n-128 289 0\n-439 118 121 124 127 131 134 145 147 152 154 0\n-11 -93 -156 0\n-202 -212 199 0\n-60 222 0\n-84 -37 -152 0\n-139 -100 -50 0\n-383 204 0\n-194 -203 189 0\n-202 -213 200 0\n-409 320 0\n-38 -160 0\n-376 131 133 145 146 0\n-57 219 0\n-405 96 103 54 61 0\n-9 -133 -95 0\n-280 -306 278 0\n2 21 55 73 110 128 0\n-358 147 154 0\n-317 -269 318 0\n-217 -238 219 0\n-354 76 77 0\n-399 241 0\n-254 -262 248 0\n-438 66 72 79 86 93 100 0\n-334 -138 -8 0\n-320 -294 323 0\n-268 0\n-207 -193 208 0\n-310 -271 313 0\n-64 -142 0\n-438 61 62 63 64 65 66 0\n-124 -86 -48 0\n-242 -227 247 0\n17 29 69 82 124 137 0\n-240 -263 235 0\n-94 255 0\n-271 -295 275 0\n186 238 293 0\n-398 189 0\n-307 0\n-77 -147 -49 0\n-285 -297 283 0\n-132 -93 -49 0\n-164 -186 166 0\n368 369 370 0\n-290 -277 291 0\n-40 -149 0\n419 420 421 0\n-217 -239 220 0\n-419 182 0\n440 441 442 0\n-267 -250 264 0\n-92 -146 0\n-122 283 0\n-182 -162 183 0\n-25 187 0\n-1 -115 0\n-423 84 85 81 106 107 102 57 58 53 0\n-33 -140 0\n-68 -130 0\n-1 -119 -87 0\n-347 171 0\n-289 -272 292 0\n395 396 397 0\n-289 -270 291 0\n-204 -171 206 0\n-439 117 118 120 121 123 124 126 127 144 145 146 147 0\n-263 -223 265 0\n-320 -293 322 0\n-255 -217 258 0\n-32 -139 0\n-52 215 0\n-92 -154 -51 0\n-119 -37 -95 0\n214 267 322 0\n-43 -139 0\n-204 -173 208 0\n-185 -191 184 0\n37 92 146 0\n13 47 66 102 121 156 0\n-25 -78 0\n-403 146 141 142 161 155 156 0\n-74 235 0\n-160 322 0\n-247 -264 243 0\n398 399 400 0\n-381 92 93 87 0\n-258 -238 260 0\n-1 -117 -73 0\n-393 232 0\n-430 313 0\n-373 123 124 125 0\n-166 -202 168 0\n-302 -317 296 0\n-242 -223 244 0\n-23 -139 -97 0\n-244 0\n-256 -223 258 0\n178 230 285 0\n-297 -282 302 0\n-340 -68 -101 0\n-439 121 127 134 140 147 154 0\n425 426 427 0\n207 259 314 0\n-211 -180 215 0\n-445 140 137 147 143 154 150 114 109 121 116 0\n-23 -131 0\n-360 94 101 0\n-119 -142 0\n-364 156 108 0\n-173 -202 175 0\n-280 -303 276 0\n-389 173 0\n-287 -311 283 0\n-399 84 85 80 106 107 101 0\n-11 -88 0\n173 225 280 0\n-196 -162 197 0\n-196 -165 200 0\n-312 -286 315 0\n-258 -240 261 0\n-68 229 0\n3 27 56 80 111 135 0\n-414 61 62 63 64 65 0\n26 49 79 104 134 158 0\n-420 79 73 86 80 93 87 100 94 0\n-294 -316 295 0\n-262 -218 266 0\n-163 -181 168 0\n422 423 424 0\n-313 -293 315 0\n-97 258 0\n-197 -171 199 0\n-298 -284 299 0\n-303 -270 305 0\n179 231 286 0\n-86 247 0\n-4 -87 0\n-8 -126 -95 0\n-78 -133 0\n-254 -263 249 0\n-34 -141 0\n-87 248 0\n-125 -143 0\n-416 181 0\n-7 169 0\n-428 45 39 42 13 7 9 20 14 16 0\n-1 162 0\n-67 228 0\n-402 88 95 102 53 0\n-293 -305 291 0\n212 265 320 0\n-3 -86 -155 0\n-407 46 47 49 14 15 16 0\n-62 -26 -156 0\n-253 -255 248 0\n-333 -23 -1 334 0\n-438 61 66 75 79 82 86 89 93 96 100 0\n-188 -210 183 0\n-23 -83 0\n-185 -193 186 0\n-251 -239 253 0\n-117 -78 -40 0\n-425 37 34 35 36 52 46 47 48 0\n-162 -175 168 0\n-403 142 149 156 108 0\n-423 85 86 81 92 93 88 58 59 53 0\n-238 -254 240 0\n-101 262 0\n-79 -158 0\n347 348 349 0\n-224 -241 222 0\n-441 235 0\n-229 -239 232 0\n-18 -147 -103 0\n-171 -187 174 0\n-442 129 136 142 149 156 108 0\n-55 -128 0\n-396 76 78 79 91 92 93 0\n-311 -278 313 0\n165 218 272 0\n-302 -318 297 0\n-64 225 0\n-96 257 0\n-82 243 0\n-222 0\n-87 -141 0\n-447 251 0\n-403 147 142 154 149 114 108 0\n-393 70 71 77 78 84 85 0\n-1 -23 325 0\n449 450 451 0\n-151 313 0\n-392 180 0\n-274 -316 275 0\n-442 131 132 128 129 152 153 148 149 159 160 155 156 0\n-40 204 0\n-420 76 77 73 98 99 94 105 106 101 0\n-445 138 139 137 160 161 157 112 113 109 119 120 116 0\n-428 45 39 40 41 42 0\n-24 186 0\n-293 -309 295 0\n-81 242 0\n-104 265 0\n-271 -290 269 0\n-226 -255 222 0\n195 247 302 0\n-239 -256 235 0\n-68 -134 -48 0\n-24 -77 0\n365 366 367 0\n-203 -164 206 0\n-1 -63 -135 0\n-343 -8 -100 344 0\n-192 0\n11 35 64 88 119 142 0\n-251 -237 252 0\n-288 -318 283 0\n-209 -211 205 0\n-323 0\n-437 175 0\n-423 85 81 92 88 107 102 58 53 0\n6 46 59 101 114 155 0\n-451 152 159 111 118 124 131 0\n-47 -156 0\n-84 245 0\n-426 92 87 88 89 107 101 102 103 0\n-66 -156 0\n-394 123 124 126 144 145 146 0\n-9 -78 -149 0\n-250 -230 252 0\n-319 -286 322 0\n-65 -45 -156 0\n-120 -149 0\n-132 -37 -97 0\n-308 -314 307 0\n-62 -134 -47 0\n-58 220 0\n-448 146 147 141 143 144 120 121 115 116 117 0\n-150 312 0\n-1 -146 341 0\n-34 -112 0\n-408 101 102 103 104 0\n-65 -95 0\n-172 -194 174 0\n-454 157 158 159 160 109 110 111 112 116 117 118 119 0\n-126 287 0\n-309 -321 307 0\n-23 185 0\n-55 -26 -155 0\n-78 -97 0\n-186 -198 184 0\n-37 201 0\n-148 310 0\n-369 61 63 75 76 0\n-49 -79 0\n-11 173 0\n-245 -250 243 0\n-93 254 0\n-213 -193 214 0\n-221 0\n-162 -171 164 0\n-402 249 0\n-5 -39 0\n-10 -84 -142 0\n-361 310 0\n-77 -144 0\n-45 -154 0\n404 405 406 0\n-423 81 88 95 102 53 0\n-342 -68 -155 0\n-195 -211 191 0\n-203 -162 204 0\n-94 -148 0\n-280 -309 282 0\n-431 46 47 49 50 14 15 16 17 0\n-420 234 0\n-159 321 0\n-231 -249 228 0\n-38 202 0\n-439 116 117 118 121 143 144 145 147 150 151 152 154 0\n-117 -26 -102 0\n-2 -79 -155 0\n-442 134 129 140 136 147 142 154 149 114 108 0\n-417 233 0\n-229 -238 231 0\n-70 231 0\n-110 -128 0\n-68 -26 -157 0\n-172 -193 173 0\n-62 -25 -149 0\n33 50 86 105 140 159 0\n-93 -160 0\n-434 167 0\n19 41 71 96 126 150 0\n-119 -92 -40 0\n-267 -253 268 0\n-8 -72 -156 0\n-168 0\n-367 271 0\n-246 -258 244 0\n-170 -179 173 0\n-127 -157 0\n-304 -282 309 0\n-143 305 0\n-345 -8 -1 346 0\n-439 116 118 120 121 130 131 133 134 143 145 146 147 0\n-210 -170 211 0\n-278 -295 282 0\n-391 280 0\n18 36 70 89 125 143 0\n-448 147 142 144 154 149 151 114 108 110 127 122 123 0\n-308 -313 306 0\n-1 -1 324 0\n-290 -280 293 0\n25 42 78 97 133 151 0\n20 48 72 103 127 157 0\n-103 -157 0\n-410 4 11 18 24 31 0\n-425 37 38 34 35 36 0\n-391 116 117 118 119 0\n-8 170 0\n-429 95 96 97 102 103 104 53 54 55 0\n-95 256 0\n452 453 454 0\n-95 -149 0\n-1 -37 331 0\n-153 315 0\n-51 -147 0\n-304 -281 308 0\n-8 -70 -142 0\n-109 270 0\n-72 -157 0\n-442 131 133 129 145 146 142 159 161 156 111 113 108 0\n-282 -322 280 0\n-314 -302 316 0\n-355 293 0\n-317 -271 320 0\n-197 -172 200 0\n-8 -127 -102 0\n-79 240 0\n-78 -151 0\n-9 171 0\n-344 -68 -101 0\n-37 -100 -160 0\n-245 -253 246 0\n-367 108 110 122 123 0\n-425 34 35 36 39 40 41 46 47 48 0\n-10 172 0\n-229 -235 228 0\n-117 -23 -81 0\n-63 -136 0\n-8 -68 -129 0\n-184 0\n-281 -312 277 0\n-262 -219 267 0\n-366 217 0\n-56 218 0\n-442 131 133 134 128 129 145 146 147 141 142 0\n-257 -233 261 0\n-187 -209 188 0\n-445 139 137 146 143 161 157 113 109 120 116 0\n-3 165 0\n-439 282 0\n407 408 409 0\n-363 263 0\n-64 -119 0\n-329 -8 -92 330 0\n-314 -296 310 0\n181 233 288 0\n-282 -320 278 0\n-232 -259 230 0\n-376 294 0\n-26 188 0\n-397 131 132 134 152 153 154 0\n-147 -160 0\n-85 246 0\n191 243 298 0\n-293 -303 289 0\n-236 0\n-54 216 0\n-208 0\n-127 288 0\n-173 -196 169 0\n-2 -77 -141 0\n-23 -84 -144 0\n-239 -259 237 0\n-308 -312 305 0\n-135 296 0\n-376 131 132 133 0\n386 387 388 0\n-48 -157 0\n-31 -138 0\n45 100 154 0\n-380 34 39 46 0\n-452 214 0\n-269 -282 275 0\n-395 188 0\n-314 -297 311 0\n-326 -68 -37 0\n-56 -33 -155 0\n-373 286 0\n-445 138 137 153 150 160 157 112 109 119 116 0\n-341 -8 -154 342 0\n-92 253 0\n-452 46 51 7 11 14 18 21 24 27 31 0\n-262 -220 268 0\n-118 279 0\n-378 84 85 86 0\n-317 -270 319 0\n-290 -282 295 0\n-45 -100 0\n-12 174 0\n-25 -133 0\n-411 219 0\n-420 76 77 78 79 73 0\n-403 304 0\n-273 -309 275 0\n-365 164 0\n-219 -250 216 0\n-385 148 149 155 156 0\n-411 53 57 67 70 74 77 81 84 0\n-374 24 25 31 32 0\n383 384 385 0\n31 84 138 0\n-310 -272 314 0\n-112 273 0\n-381 248 0\n-272 -301 274 0\n-121 -156 0\n-274 -313 271 0\n171 223 278 0\n-417 69 70 71 72 76 77 78 79 0\n-230 -242 228 0\n-421 131 132 134 128 152 153 154 148 0\n-31 193 0\n-428 206 0\n-359 39 46 0\n-311 -282 316 0\n-450 259 0\n-55 -133 -39 0\n-107 268 0\n-337 -23 -1 338 0\n-1 -66 -155 0\n-167 -209 168 0\n-265 -238 267 0\n-18 179 0\n-273 -304 269 0\n-219 -253 220 0\n-189 -162 190 0\n-11 -142 0\n-313 -289 310 0\n-320 -289 317 0\n-380 37 34 52 46 0\n392 393 394 0\n-1 -92 343 0\n-289 -274 294 0\n-88 -119 0\n-254 -264 250 0\n-55 -73 0\n-424 297 0\n-423 84 81 99 95 106 102 57 53 0\n-78 239 0\n-439 116 118 121 130 131 134 143 145 147 150 152 154 0\n-243 -229 244 0\n-206 -185 207 0\n-57 -87 0\n-278 -289 276 0\n371 372 373 0\n-42 206 0\n-436 274 0\n-124 285 0\n-385 149 156 108 0\n-281 -314 279 0\n-41 205 0\n-157 319 0\n-176 -162 177 0\n-8 -71 -149 0\n-230 -245 231 0\n-86 -140 0\n-299 0\n-428 45 39 40 42 20 14 15 16 0\n-68 -25 -150 0\n-325 -8 -31 326 0\n203 255 310 0\n-9 -77 -142 0\n12 40 65 95 120 149 0\n-84 -147 -50 0\n-8 -116 0\n-47 210 0\n-25 -42 0\n-155 317 0\n-171 -185 172 0\n-453 267 0\n-13 175 0\n-209 -210 204 0\n-296 -273 300 0\n-439 116 118 119 121 130 131 132 134 150 152 153 154 0\n-311 -280 315 0\n-156 318 0\n-283 0\n-162 -170 163 0\n-199 -185 200 0\n-281 -316 282 0\n-100 -154 0\n443 444 445 0\n-103 264 0\n362 363 364 0\n-98 259 0\n-442 131 134 129 145 147 142 152 154 149 111 114 108 0\n-386 46 47 48 0\n-448 146 147 144 113 114 110 120 121 117 126 127 123 0\n-1 -46 345 0\n-318 -278 320 0\n-174 -209 175 0\n-17 178 0\n-201 -206 199 0\n-154 316 0\n-274 -311 269 0\n-212 -187 215 0\n189 241 296 0\n-249 -224 252 0\n-31 -84 0\n198 250 305 0\n-90 -132 0\n-147 309 0\n-439 116 117 118 120 121 143 144 145 146 147 0\n-394 123 124 125 126 0\n-409 155 157 158 115 116 117 0\n-432 266 0\n-372 231 0\n-152 314 0\n-362 210 0\n-420 76 79 73 91 93 87 98 100 94 0\n-349 117 123 0\n-421 131 133 134 128 145 146 147 141 0\n-54 -109 0\n-201 -203 196 0\n-286 -304 283 0\n167 220 274 0\n-260 0\n-62 -23 -136 0\n-384 256 0\n377 378 379 0\n-179 -197 177 0\n-282 -317 276 0\n-261 -264 257 0\n-397 131 133 134 145 146 147 0\n-346 -68 -8 0\n-298 -288 302 0\n-201 -204 197 0\n-35 197 0\n-68 -24 -143 0\n-314 -300 315 0\n-338 -138 -8 0\n416 417 418 0\n431 432 433 0\n205 257 312 0\n-421 131 132 133 128 159 160 161 155 0\n-139 301 0\n-45 209 0\n410 411 412 0\n-262 -216 264 0\n-312 -285 314 0\n-80 241 0\n-245 -251 244 0\n-316 -320 313 0\n-442 131 132 134 129 152 153 154 149 111 112 114 108 0\n-138 -93 -50 0\n-29 191 0\n-71 232 0\n-418 288 0\n-133 294 0\n-449 207 0\n-438 227 0\n-110 -23 -80 0\n-102 -156 0\n-34 -87 0\n-306 -294 308 0\n-88 -142 0\n-38 -147 0\n-113 -45 -101 0\n446 447 448 0\n-85 -139 0\n-285 -302 288 0\n-351 230 0\n32 43 85 98 139 152 0\n-365 2 9 16 0\n199 251 306 0\n-389 9 11 16 18 30 31 0\n-449 45 39 40 41 42 43 0\n-430 151 158 110 117 123 0\n-84 -138 0\n-62 -132 -35 0\n-409 158 110 117 123 0\n-220 -257 216 0\n-68 -75 0\n-169 0\n-101 -155 0\n-64 -88 0\n-11 -92 -149 0\n-397 295 0\n-390 225 0\n-353 24 31 0\n197 249 304 0\n-217 -240 221 0\n-270 -288 275 0\n-242 -225 245 0\n-163 -178 165 0\n-229 -240 233 0\n-133 -151 0\n-102 263 0\n-386 211 0\n-202 -210 197 0\n-215 0\n-173 -201 174 0\n-201 -207 200 0\n-170 -178 172 0\n-41 -150 0\n-117 -79 -47 0\n-296 -271 299 0\n-149 311 0\n-220 -261 221 0\n-79 -104 0\n-265 -239 268 0\n-223 -239 226 0\n-158 320 0\n-55 -132 -34 0\n-288 -322 286 0\n-17 -138 -89 0\n-429 258 0\n-239 -257 236 0\n-401 197 0\n-407 212 0\n-93 -147 0\n-269 -281 274 0\n-39 -113 0\n-110 -78 -39 0\n-223 -240 227 0\n10 28 63 81 118 136 0\n-161 323 0\n-291 0\n-406 150 157 109 116 0\n-380 196 0\n-378 85 86 92 93 0\n-9 -79 -156 0\n-225 -248 222 0\n-289 -273 293 0\n-88 249 0\n-357 254 0\n-338 -84 -8 0\n-364 318 0\n-272 -302 275 0\n-375 239 0\n-324 -61 -8 0\n-448 306 0\n-447 87 88 89 90 94 95 96 97 101 102 103 104 0\n-8 -124 -81 0\n-34 196 0\n-454 158 159 160 110 111 112 117 118 119 123 124 125 0\n389 390 391 0\n-315 0\n-1 -120 -94 0\n-9 -132 -88 0\n-390 61 62 64 82 83 84 0\n-407 46 49 7 9 14 16 0\n-233 -266 230 0\n-371 16 18 30 31 0\n-28 190 0\n183 235 290 0\n-355 131 132 0\n-406 312 0\n-132 293 0\n-447 93 87 88 89 90 100 94 95 96 97 0\n-448 147 143 144 154 150 151 114 109 110 121 116 117 0\n-286 -306 284 0\n-425 38 34 35 36 45 39 40 41 0\n-408 102 103 104 53 54 55 0\n164 217 271 0\n-73 234 0\n-409 156 158 108 110 122 123 0\n380 381 382 0\n-316 -322 315 0\n413 414 415 0\n-226 -261 227 0\n-188 -211 184 0\n-47 -102 0\n-200 0\n-228 0\n-6 168 0\n-371 179 0\n-138 -37 -98 0\n-2 -132 -87 0\n8 0\n-55 217 0\n9 22 62 74 117 129 0\n-442 131 132 133 134 128 129 0\n-415 116 118 120 130 131 133 143 145 146 0\n-18 -89 0\n-397 131 134 145 147 152 154 0\n-442 131 133 128 129 145 146 141 142 159 161 155 156 0\n-65 226 0\n-399 80 87 94 101 0\n-20 181 0\n-62 -133 -40 0\n-383 45 39 40 0\n-448 144 151 158 110 117 123 0\n-402 92 88 107 102 58 53 0\n-436 108 110 111 113 122 123 124 126 142 144 145 146 0\n-253 -259 252 0\n-219 -254 221 0\n-295 -319 291 0\n-450 98 105 56 63 69 76 0\n-388 157 109 116 0\n-405 257 0\n-438 61 63 64 66 75 76 77 79 96 98 99 100 0\n-210 -174 215 0\n-134 295 0\n-68 -132 -36 0\n-89 -125 0\n-91 252 0\n-429 94 95 96 97 101 102 103 104 0\n38 51 93 106 147 160 0\n-403 146 147 142 113 114 108 0\n-70 -37 -150 0\n-294 -312 291 0\n-22 183 0\n-448 146 147 143 144 113 114 109 110 120 121 116 117 0\n-48 211 0\n-78 -45 -158 0\n182 234 289 0\n-428 39 42 46 49 7 9 14 16 0\n-14 176 0\n-448 147 144 154 151 114 110 121 117 127 123 0\n-395 26 33 38 45 0\n206 258 313 0\n-327 -8 -31 328 0\n-447 88 89 90 95 96 97 102 103 104 53 54 55 0\n-303 -272 307 0\n-27 189 0\n-136 297 0\n-385 311 0\n-23 -76 0\n-360 100 94 0\n166 219 273 0\n-275 0\n-174 -203 169 0\n-332 -68 -101 333 0\n-63 224 0\n-111 272 0\n-264 -231 267 0\n-257 -229 258 0\n-24 -146 -97 0\n-51 214 0\n-339 -8 -100 340 0\n-422 190 0\n-387 264 0\n-321 -298 319 0\n-420 76 77 79 73 98 99 100 94 0\n-292 -298 291 0\n-117 -25 -95 0\n-234 -216 236 0\n-144 306 0\n-23 -86 -158 0\n-265 -234 262 0\n-294 -314 292 0\n-2 -134 -101 0\n-39 -94 0\n-403 146 147 141 142 0\n-121 282 0\n-273 -306 271 0\n-100 261 0\n-293 -308 294 0\n-69 230 0\n-96 -126 0\n-119 -93 -47 0\n-23 -138 -90 0\n-374 187 0\n-404 205 0\n-454 155 157 158 159 160 115 116 117 118 119 0\n-301 -313 299 0\n190 242 297 0\n-417 69 71 72 76 78 79 91 92 93 0\n-196 -164 199 0\n-454 155 156 157 158 159 160 0\n-71 -150 0\n-78 -154 -49 0\n-5 -100 -155 0\n-68 -23 -137 0\n-218 -247 221 0\n-32 194 0\n-39 203 0\n-405 94 96 101 103 60 61 0\n-439 116 117 118 119 121 150 151 152 153 154 0\n-42 -78 0\n-49 212 0\n-247 -262 241 0\n-267 -251 265 0\n-306 -289 303 0\n174 226 281 0\n-431 46 47 48 49 50 0\n-352 285 0\n-112 -141 0\n-310 -270 312 0\n-382 147 141 154 148 0\n-387 101 103 60 61 0\n-374 25 32 37 0\n-381 92 87 107 101 0\n-113 274 0\n-238 -250 236 0\n210 263 318 0\n-1 -84 329 0\n428 429 430 0\n-164 -188 168 0\n-446 199 0\n-334 -84 -8 0\n-418 123 124 126 127 144 145 146 147 0\n-274 -312 270 0\n-417 69 70 72 76 77 79 98 99 100 0\n353 354 355 0\n-32 -85 0\n-209 -214 208 0\n-24 -132 0\n-261 -265 258 0\n-5 -154 -101 0\n-138 300 0\n-316 -319 312 0\n-454 155 157 159 160 115 116 118 119 128 130 131 132 0\n-302 -320 299 0\n-19 180 0\n-421 289 0\n-451 314 0\n-418 127 134 140 147 154 0\n-426 250 0\n-257 -231 260 0\n-309 -319 305 0\n-232 -256 228 0\n-288 -320 284 0\n-18 -146 -96 0\n-438 61 62 64 66 82 83 84 86 96 97 99 100 0\n-198 -178 200 0\n-9 -134 -102 0\n-404 45 39 40 41 0\n-62 -117 0\n-442 131 132 133 134 129 111 112 113 114 108 0\n-400 296 0\n-442 131 128 129 145 141 142 152 148 149 159 155 156 0\n-317 -273 322 0\n-435 220 0\n-252 0\n-322 -306 320 0\n-442 131 132 129 152 153 149 159 160 156 111 112 108 0\n374 375 376 0\n-316 -321 314 0\n-262 -217 265 0\n-187 -203 182 0\n"
 "1103 -330 -100 0 33 64 0\n1104 -15 0 66 37 0\n1105 -108 0 69 0\n1106 -123 0 33 130 0\n1107 -328 -37 0 33 161 0\n1108 -133 -41 0 33 171 0\n1109 -442 131 129 145 142 152 149 159 156 111 0 1105 176 0\n1110 -403 146 142 161 156 113 0 1105 178 0\n1111 -30 0 185 31 0\n1112 -53 0 185 75 0\n1113 1 0 1112 1105 29 0\n1114 327 0 1113 185 157 0\n1115 -442 131 133 134 129 145 146 147 142 111 113 114 0 1105 187 0\n1116 -442 131 132 133 129 159 160 161 156 111 112 113 0 1105 196 0\n1117 -410 2 4 9 11 16 18 31 0 1111 201 0\n1118 -55 -135 0 185 210 0\n1119 -412 109 110 111 112 0 1105 227 0\n1120 -65 -148 0 1113 228 0\n1121 -16 0 33 243 0\n1122 -145 0 286 106 0\n1123 -115 0 1113 303 0\n1124 -423 84 85 81 106 107 102 57 58 0 1112 304 0\n1125 -130 0 33 306 0\n1126 -119 -87 0 1113 307 0\n1127 -439 117 118 120 121 124 126 127 144 146 147 0 1106 1122 313 0\n1128 -117 -73 0 1113 335 0\n1129 -373 124 125 0 1106 338 0\n1130 -139 -97 0 185 342 0\n1131 -340 -101 0 33 347 0\n1132 -131 0 185 353 0\n1133 -364 156 0 1105 356 0\n1134 -280 -303 0 224 358 0\n1135 229 0 33 368 0\n1136 -428 45 39 42 13 7 9 20 14 0 1121 393 0\n1137 162 0 1113 394 0\n1138 -402 88 95 102 0 1112 396 0\n1139 -407 46 47 49 14 0 1104 1121 400 0\n1140 -333 334 0 185 1113 403 0\n1141 -83 0 185 406 0\n1142 -175 168 0 1137 411 0\n1143 -403 142 149 156 0 1105 412 0\n1144 -423 85 86 81 92 93 88 58 59 0 1112 413 0\n1145 -239 232 0 1135 420 0\n1146 -442 129 136 142 149 156 0 1105 423 0\n1147 -60 0 432 250 0\n1148 -403 147 142 154 149 114 0 1105 435 0\n1149 325 0 1113 185 437 0\n1150 -442 132 128 129 152 153 148 149 159 160 155 156 0 1132 442 0\n1151 -226 -255 0 432 452 0\n1152 -134 -48 0 33 455 0\n1153 -63 -135 0 1113 459 0\n1154 -423 85 81 92 88 107 102 58 0 1112 468 0\n1155 -451 152 159 111 118 124 0 1132 470 0\n1156 -394 124 126 144 146 0 1106 1122 475 0\n1157 -308 -314 0 286 482 0\n1158 -448 146 147 141 143 144 120 121 116 117 0 1123 485 0\n1159 -146 341 0 1113 487 0\n1160 -309 -321 0 286 494 0\n1161 185 0 185 495 0\n1162 -59 0 507 105 0\n1163 -171 164 0 1137 508 0\n1164 -423 81 88 95 102 0 1112 516 0\n1165 -342 -155 0 33 517 0\n1166 -203 204 0 1137 519 0\n1167 -431 46 47 49 50 14 17 0 1104 1121 522 0\n1168 -439 116 117 118 121 143 144 147 150 151 152 154 0 1122 527 0\n1169 -442 134 129 140 136 147 142 154 149 114 0 1105 530 0\n1170 -238 231 0 1135 532 0\n1171 -26 -157 0 33 535 0\n1172 -267 -253 0 273 543 0\n1173 -175 0 545 1142 0\n1174 -437 0 1173 467 0\n1175 -246 -258 0 343 547 0\n1176 -345 -8 346 0 1113 552 0\n1177 -439 116 118 120 121 133 134 143 146 147 0 1125 1132 1122 553 0\n1178 -448 147 142 144 154 149 151 114 110 127 122 0 1105 1106 558 0\n1179 324 0 1113 560 0\n1180 -429 95 96 97 102 103 104 54 55 0 1112 569 0\n1181 -37 331 0 1113 573 0\n1182 -442 133 129 146 142 159 161 156 111 113 0 1132 1122 1105 580 0\n1183 -344 -101 0 33 590 0\n1184 -367 110 122 0 1105 1106 593 0\n1185 -235 228 0 1135 596 0\n1186 -117 -81 0 185 597 0\n1187 -8 -129 0 33 599 0\n1188 -191 0 600 1161 324 0\n1189 -443 0 1188 150 0\n1190 -442 133 134 128 129 146 147 141 142 0 1132 1122 605 0\n1191 -397 132 134 152 153 154 0 1132 621 0\n1192 243 298 0 1188 624 0\n1193 -44 0 628 219 0\n1194 -84 -144 0 185 632 0\n1195 -376 132 133 0 1132 636 0\n1196 -326 -37 0 33 646 0\n1197 -262 -220 0 273 653 0\n1198 -411 57 67 70 74 77 81 84 0 1112 668 0\n1199 -421 132 134 128 152 153 154 148 0 1132 681 0\n1200 -107 0 273 688 0\n1201 -337 338 0 185 1113 689 0\n1202 -66 -155 0 1113 690 0\n1203 -167 -209 0 545 691 0\n1204 -189 190 0 1137 696 0\n1205 -92 343 0 1113 702 0\n1206 -423 84 81 99 95 106 102 57 0 1112 708 0\n1207 -439 116 118 121 134 143 147 150 152 154 0 1125 1132 1122 710 0\n1208 -243 0 1135 343 711 0\n1209 -444 0 1208 237 0\n1210 -82 0 1208 431 0\n1211 298 0 1208 1192 0\n1212 -206 207 0 1161 712 0\n1213 -278 -289 0 224 714 0\n1214 -385 149 156 0 1105 719 0\n1215 -176 0 1137 66 723 0\n1216 -284 0 727 1211 380 0\n1217 -428 45 39 40 42 20 14 0 1104 1121 728 0\n1218 -25 -150 0 33 729 0\n1219 -8 -31 326 0 1149 730 0\n1220 -171 172 0 1161 739 0\n1221 -13 0 1173 741 0\n1222 -439 116 118 119 121 132 134 150 152 153 154 0 1125 1132 744 0\n1223 -122 0 747 300 0\n1224 -170 163 0 1137 748 0\n1225 -199 200 0 1161 749 0\n1226 445 0 1189 1209 752 0\n1227 -442 134 129 147 142 152 154 149 111 114 0 1132 1122 1105 756 0\n1228 -448 146 147 144 113 114 110 120 121 117 126 127 0 1106 758 0\n1229 -46 345 0 1113 759 0\n1230 -174 -209 0 1173 761 0\n1231 -439 116 117 118 120 121 143 144 146 147 0 1122 773 0\n1232 -394 124 125 126 0 1106 774 0\n1233 -409 155 157 158 116 117 0 1123 775 0\n1234 -349 117 0 1106 781 0\n1235 -421 133 134 128 146 147 141 0 1132 1122 782 0\n1236 -286 -304 0 747 785 0\n1237 -99 0 787 129 0\n1238 -62 -136 0 185 788 0\n1239 -179 -197 0 66 791 0\n1240 -282 -317 0 224 792 0\n1241 -397 133 134 146 147 0 1132 1122 794 0\n1242 -346 -8 0 33 795 0\n1243 -288 302 0 1211 796 0\n1244 -24 -143 0 33 799 0\n1245 -421 132 133 128 159 160 161 155 0 1132 805 0\n1246 -245 -251 0 343 812 0\n1247 -442 132 134 129 152 153 154 149 111 112 114 0 1132 1105 814 0\n1248 -29 0 1188 816 0\n1249 -110 -80 0 185 822 0\n1250 -365 2 9 0 1121 834 0\n1251 -389 9 11 18 31 0 1121 1111 836 0\n1252 -430 151 158 110 117 0 1106 838 0\n1253 -409 158 110 117 0 1106 841 0\n1254 -75 0 33 843 0\n1255 -7 0 844 392 0\n1256 -217 -240 0 507 852 0\n1257 -240 233 0 1135 856 0\n1258 -52 0 861 318 0\n1259 -296 -271 0 727 867 0\n1260 -220 -261 0 507 869 0\n1261 -265 -239 0 273 871 0\n1262 -239 -257 0 626 878 0\n1263 -161 0 466 887 0\n1264 -225 -248 0 432 893 0\n1265 -61 -8 0 1179 901 0\n1266 -454 158 159 160 110 111 112 117 118 119 124 125 0 1106 906 0\n1267 -153 0 908 574 0\n1268 -120 -94 0 1113 909 0\n1269 -390 61 62 64 84 0 1210 1141 911 0\n1270 -407 46 49 9 14 0 1255 1121 912 0\n1271 -371 18 31 0 1121 1111 914 0\n1272 -355 132 0 1132 917 0\n1273 -286 -306 0 1216 922 0\n1274 -408 102 103 104 54 55 0 1112 924 0\n1275 -409 156 158 110 0 1105 1223 1106 927 0\n1276 -316 -322 0 908 929 0\n1277 -188 -211 0 600 932 0\n1278 -199 0 934 1225 0\n1279 -67 0 935 395 0\n1280 -235 0 935 1185 0\n1281 -74 0 1280 329 0\n1282 -441 0 1280 419 0\n1283 -6 0 545 936 0\n1284 170 0 940 568 0\n1285 -129 0 940 1187 0\n1286 -116 0 940 735 0\n1287 -346 0 940 1242 0\n1288 -61 0 940 1265 0\n1289 -183 0 1284 600 103 0\n1290 -190 0 1284 1188 191 0\n1291 163 0 1284 1224 0\n1292 -345 0 1287 940 1176 0\n1293 -440 0 1289 182 0\n1294 -182 0 1289 1137 301 0\n1295 290 0 1289 1280 916 0\n1296 -189 0 1290 1204 0\n1297 -28 0 1290 915 0\n1298 -181 0 1291 545 375 0\n1299 -46 0 1292 1229 0\n1300 442 0 1293 1282 297 0\n1301 -21 0 1294 77 0\n1302 -419 0 1294 296 0\n1303 -277 0 1295 888 292 0\n1304 -398 0 1296 285 0\n1305 -416 0 1298 391 0\n1306 -279 0 1303 1211 48 0\n1307 -370 0 1306 233 0\n1308 -118 0 1306 654 0\n1309 9 22 62 117 0 1281 1285 942 0\n1310 132 133 134 128 0 1300 1132 1285 943 0\n1311 -415 120 133 143 146 0 1286 1308 1125 1132 1122 944 0\n1312 -397 134 147 152 154 0 1132 1122 946 0\n1313 133 128 146 141 142 159 155 156 0 1300 1132 1285 1122 1263 947 0\n1314 -20 0 1298 950 0\n1315 -448 144 151 158 110 117 0 1106 953 0\n1316 -402 92 88 102 58 0 1200 1112 954 0\n1317 -436 110 111 113 124 126 142 144 146 0 1105 1223 1106 1122 955 0\n1318 -219 -254 0 507 957 0\n1319 -295 -319 0 888 958 0\n1320 -388 157 109 0 1286 960 0\n1321 -438 63 64 66 76 77 79 96 98 100 0 1288 1254 1237 962 0\n1322 -210 -174 0 861 963 0\n1323 -132 -36 0 33 965 0\n1324 -403 146 147 142 113 114 0 1105 970 0\n1325 -294 -312 0 888 972 0\n1326 -22 0 1289 973 0\n1327 -448 146 147 143 144 113 114 109 110 120 121 117 0 1286 974 0\n1328 234 289 0 1294 977 0\n1329 -428 39 42 49 9 14 0 1299 1255 1121 978 0\n1330 -14 0 1215 979 0\n1331 -448 147 144 154 151 114 110 121 117 127 0 1106 980 0\n1332 -31 328 0 1114 940 983 0\n1333 -447 88 89 90 95 96 97 102 103 104 54 55 0 1112 984 0\n1334 -303 -272 0 286 985 0\n1335 -27 0 1296 986 0\n1336 -76 0 185 989 0\n1337 -114 0 992 123 0\n1338 -174 -203 0 844 993 0\n1339 -332 -101 333 0 33 994 0\n1340 -257 258 0 1135 998 0\n1341 -339 -100 340 0 940 1001 0\n1342 -422 0 1290 1002 0\n1343 -321 319 0 1211 1004 0\n1344 -420 77 79 73 98 100 94 0 1336 1237 1005 0\n1345 -292 0 1211 888 1006 0\n1346 -234 -216 0 626 1008 0\n1347 -86 -158 0 185 1010 0\n1348 -294 -314 0 1345 1012 0\n1349 -138 -90 0 185 1023 0\n1350 -454 155 157 158 159 160 117 119 0 1123 1286 1308 1026 0\n1351 -301 -313 0 727 1027 0\n1352 242 297 0 1290 1028 0\n1353 -417 69 71 72 78 79 91 92 93 0 1336 1029 0\n1354 -196 -164 0 1278 1030 0\n1355 -137 0 33 185 1035 0\n1356 -218 -247 0 507 1036 0\n1357 -405 94 96 101 103 0 1147 1288 1039 0\n1358 -439 117 119 121 150 151 152 154 0 1286 1308 1267 1040 0\n1359 -431 47 48 49 50 0 1299 1047 0\n1360 -387 101 103 0 1147 1288 1052 0\n1361 -381 92 87 101 0 1200 1054 0\n1362 -238 -250 0 626 1056 0\n1363 -84 329 0 1113 1058 0\n1364 -164 -188 0 545 1060 0\n1365 -446 0 1278 1061 0\n1366 -334 -84 0 940 1062 0\n1367 -418 124 126 127 144 146 147 0 1106 1122 1063 0\n1368 -417 69 70 72 77 79 98 100 0 1336 1237 1065 0\n1369 -209 -214 0 628 1068 0\n1370 -454 155 157 159 160 119 128 132 0 1123 1286 1308 1125 1132 1074 0\n1371 -302 -320 0 727 1075 0\n1372 -257 -231 0 787 1081 0\n1373 -232 -256 0 935 1083 0\n1374 -288 -320 0 1216 1084 0\n1375 -438 62 64 66 84 86 96 97 100 0 1288 1210 1141 1237 1086 0\n1376 -198 -178 0 934 1087 0\n1377 132 133 134 111 112 113 0 1300 1132 1285 1337 1105 1091 0\n1378 128 141 142 152 148 149 159 155 156 0 1300 1132 1285 1122 1093 0\n1379 -91 0 1096 967 0\n1380 132 152 149 159 160 156 111 112 0 1300 1132 1285 1267 1105 1098 0\n1381 -187 -203 0 1294 1102 0\n1382 -84 -332 -336 0 940 33 1337 1299 1283 1162 897 1366 1201 1140 11 1339 469 0\n1383 -267 -322 0 466 787 1113 940 33 1337 1299 1283 1162 1276 764 169 86 173 1172 1018 651 640 325 1107 184 1181 1332 80 101 1382 671 271 801 1140 1201 1339 11 469 0\n1384 -297 178 93 -138 -100 155 -454 0 1306 432 1173 1303 940 1162 1283 1299 1337 466 1365 727 747 1096 1072 104 902 829 1349 10 169 86 469 1183 460 1205 325 591 415 141 119 190 722 17 524 114 288 152 617 345 873 477 1350 89 1126 704 26 0\n1385 297 -266 -300 149 0 935 1300 1285 1298 747 987 1352 92 680 22 913 1146 616 746 464 0\n1386 -266 -138 -100 155 -454 0 1306 1303 432 1173 940 1162 1283 1299 1337 466 1096 727 1291 934 1072 10 169 86 469 1183 460 1205 325 591 415 141 119 581 1134 136 1276 685 868 190 722 17 524 40 505 1385 114 1384 152 617 855 873 365 1350 890 1126 928 333 0\n1387 -297 -138 -100 155 -454 0 1113 992 1174 1306 1303 432 1173 940 1162 1283 1299 1337 727 934 466 1308 1286 469 415 1386 374 1072 104 1009 10 169 86 1183 460 1205 325 591 141 119 581 1134 136 190 118 551 722 17 524 821 93 643 95 114 175 152 617 427 873 365 1350 1031 890 1126 746 928 137 333 221 881 1231 0\n1388 -138 -100 155 -454 0 934 940 466 1278 1162 1283 1299 1337 432 1173 1295 908 1342 935 1300 1285 1336 1200 10 1276 469 415 141 119 657 121 169 86 1183 460 1205 325 499 763 982 1175 623 863 820 685 868 1197 484 1383 602 259 209 839 938 1072 800 1078 438 1386 229 374 604 1387 707 987 1352 92 376 680 22 1020 1146 959 823 202 1124 0\n1389 -100 155 -454 0 466 1113 1174 1303 992 1162 1283 1337 432 1173 1295 934 787 1208 1278 861 1211 1306 600 1298 1342 935 1221 1330 1299 1355 1210 1248 940 461 1200 1314 10 1276 469 415 141 119 657 121 643 451 190 118 722 17 524 230 821 93 685 1197 484 1383 602 661 52 1183 95 764 169 86 460 1018 1205 931 325 1107 499 1332 763 863 982 62 1175 623 1388 671 251 472 2 63 504 1246 206 229 776 350 755 770 835 108 803 199 582 720 645 498 1376 1017 1037 98 46 1046 707 1352 447 762 81 833 629 616 1322 376 680 808 252 208 736 1020 858 326 1167 280 544 102 1042 904 348 56 1154 147 42 362 565 538 421 278 563 0\n1390 -147 17 -84 -431 -417 72 47 69 98 100 0 1330 1299 1379 1336 734 881 1167 234 502 0\n1391 -156 230 138 -92 155 -454 0 1113 1174 1306 1303 992 1162 1283 1299 432 1173 1295 1096 466 747 1298 1305 1208 1278 1365 1223 1337 1308 1286 940 1020 651 956 755 10 1276 764 1389 640 49 807 1369 469 415 141 119 657 121 439 643 451 151 190 118 551 685 868 581 1134 722 17 524 230 821 93 95 169 86 471 746 544 137 464 221 629 818 616 802 913 206 776 506 803 682 671 472 1194 504 1246 770 434 835 1376 829 825 1045 762 819 246 1390 1178 1177 355 577 177 1370 1368 134 0\n1392 297 138 -92 155 -454 0 466 1113 1174 1306 1303 1162 1283 1299 1337 432 1173 1096 935 1300 1285 1267 1308 1286 1302 651 956 755 10 1276 764 1389 640 49 807 1230 469 415 141 119 685 868 190 722 17 524 821 93 1240 95 169 987 1352 680 1391 1146 1031 22 355 207 416 873 1236 576 699 1371 1374 20 221 1046 1077 46 629 109 215 1151 294 134 1128 282 1344 0\n1393 138 -92 155 -454 0 1162 1283 1299 1337 432 1173 1096 727 1278 628 651 956 10 1276 469 415 141 119 685 581 1392 114 645 262 350 835 274 1246 682 472 671 0\n1394 -297 -92 155 -454 0 1306 1303 432 1173 992 1295 1162 1283 1299 1337 727 747 466 940 1393 1072 104 1009 10 1276 764 1389 640 49 469 415 1197 1095 807 1203 540 97 1230 659 828 141 119 643 451 151 685 868 190 722 17 524 169 86 114 288 175 152 617 718 996 873 1350 1031 355 542 746 479 1317 137 385 221 733 0\n1395 -92 155 -454 0 1306 1162 1283 1299 432 1173 934 1337 1300 1285 10 1276 764 1389 640 807 1369 1000 469 415 141 119 685 868 17 230 1383 209 49 1393 1072 1394 987 92 1385 22 206 776 1146 255 803 471 746 526 428 163 46 772 969 1169 815 102 1152 1359 0\n1396 -112 147 39 92 101 146 0 1299 96 488 1049 1361 641 68 928 0\n1397 -110 85 84 101 106 0 1200 1304 151 1249 1259 361 1092 332 0\n1398 -117 94 133 105 98 282 101 106 0 1302 1237 1336 152 1128 555 1213 964 246 1077 1310 294 134 444 0\n1399 -124 85 57 58 102 84 106 0 940 747 1200 1342 718 904 288 1124 707 376 0\n1400 -86 80 135 111 -155 0 1335 383 399 1356 369 604 0\n1401 -103 257 250 -155 0 1174 626 1208 738 1240 610 93 1202 61 753 15 331 705 793 587 383 505 1018 270 0\n1402 -64 112 4 57 34 0 1113 133 429 181 1264 389 0\n1403 -203 5 -434 37 0 1215 1296 236 254 1338 1381 1076 1037 659 302 73 0\n1404 134 132 112 133 113 0 1345 1377 1310 996 246 309 0\n1405 270 319 -25 0 600 286 1303 1286 1355 1267 1226 722 302 83 1025 1218 578 232 889 5 390 551 515 19 118 245 4 961 718 330 195 673 1372 1129 649 777 639 715 1271 0\n1406 319 132 -25 -92 0 888 992 1302 1337 1299 1283 1162 1113 432 1174 1263 1285 1300 1132 940 466 1314 1308 1286 1135 1336 660 327 651 1172 740 145 722 1343 524 1405 311 656 853 246 1077 738 629 1310 294 469 1395 177 1152 95 1131 415 571 1341 141 642 821 1369 93 807 640 764 1276 330 34 746 544 137 239 563 221 195 753 215 53 1128 692 662 117 0\n1407 132 -25 -92 0 861 1303 432 1113 1299 1283 1162 1345 466 1326 1173 992 1280 1337 1122 1285 1300 1132 1221 1336 302 766 660 327 299 1406 190 1319 119 1016 848 964 141 1310 415 158 246 469 309 1213 1202 738 996 152 107 1309 1055 589 1404 138 115 673 644 85 736 664 310 281 772 858 1115 326 732 892 60 0\n1408 -289 79 -92 -319 -25 0 1174 1162 1283 1299 466 861 1121 908 1303 1223 1336 343 1345 888 1122 1285 1300 1132 1326 432 940 1113 1210 1254 1288 1308 1301 1173 1237 1286 1337 1355 1226 1319 848 327 1407 134 60 310 644 1364 665 651 1172 209 190 119 141 415 919 377 337 302 766 1042 737 41 138 589 217 1059 877 1175 623 592 472 1397 1184 457 603 244 811 448 772 397 551 299 469 738 107 1055 1202 610 93 964 1016 1218 660 309 311 1213 996 578 152 678 1115 232 1309 88 276 355 577 1171 579 158 926 223 567 263 907 1118 359 1400 357 126 526 658 751 981 352 305 0\n1409 79 -92 -319 -25 0 861 1303 432 908 1173 1121 1223 1302 1336 1112 1407 919 377 337 651 1172 209 134 190 119 141 415 1319 848 302 766 1042 737 327 60 310 644 138 1364 589 41 665 217 1059 877 1175 623 592 472 1397 1184 457 1408 1328 1077 1346 294 627 662 143 706 0\n1410 -117 88 102 -25 0 727 1342 152 1186 1007 114 1164 707 376 0\n1411 -92 -319 -25 0 861 1303 1173 1162 1283 1299 908 626 1280 1286 1337 1355 1226 888 432 1285 1300 1326 1221 190 119 141 415 469 1202 1319 964 1016 302 766 880 1218 660 299 1407 919 377 397 448 551 772 1409 587 870 15 281 753 858 489 611 256 1371 813 46 764 352 578 311 381 246 1328 205 88 1190 132 826 1410 1309 589 892 115 326 736 0\n1412 -9 -319 -25 0 861 1303 432 1162 1283 1299 1337 466 1173 1280 1221 1379 1336 1411 190 119 141 415 469 738 107 1055 1202 1319 964 848 1016 302 1381 1038 766 660 327 589 138 115 644 85 736 310 281 858 326 892 60 425 134 881 1404 1396 673 86 111 0\n1413 -77 102 -319 -25 0 1280 1113 1326 1412 1319 964 660 117 134 100 1310 895 158 1410 1309 0\n1414 -128 9 0 1113 1326 158 246 1309 1213 152 0\n1415 -117 79 77 78 0 1336 1302 152 1128 1213 662 1077 294 0\n1416 142 111 149 147 113 342 134 133 0 1122 1132 940 1337 1300 1285 1115 86 1159 1157 650 778 1227 0\n1417 -146 109 26 79 -319 -25 0 861 1303 1173 432 1162 1283 1299 888 466 940 1286 1337 1355 1226 185 1319 964 660 1412 1414 1310 919 448 772 397 551 190 119 141 415 469 1165 1016 302 766 1042 1218 86 1159 169 650 315 352 873 154 371 0\n1418 79 102 -319 -25 0 600 1303 1173 1162 1283 1337 466 1336 1289 1221 1326 432 1302 1345 888 1355 1226 1308 1286 1299 1200 1208 1210 1254 1288 1413 1319 964 660 1412 1414 1310 919 448 772 397 551 216 1323 1411 190 119 141 415 469 738 107 1055 1202 1165 848 1016 302 1381 1038 83 721 67 443 1218 327 60 310 644 405 1277 736 975 326 1415 1309 132 537 840 401 88 523 1328 294 309 311 996 578 232 564 1416 276 355 697 826 567 1417 325 1235 1107 388 433 1332 594 349 1080 473 504 945 472 1251 223 907 0\n1419 -367 -319 -25 0 1303 1173 432 908 1223 1319 964 660 1412 1414 1310 919 377 190 119 141 415 302 1381 13 546 1184 275 65 512 354 122 0\n1420 79 -319 -25 0 466 1326 940 1300 1285 935 343 1305 747 1106 1319 964 660 1412 1414 1310 134 226 493 327 1415 1418 1309 823 858 586 132 1238 537 1146 208 341 22 531 1352 1236 802 288 20 38 718 0\n1421 -319 -25 0 1303 1173 432 1337 1299 1283 1162 190 119 141 415 469 1412 1419 1420 529 587 1250 1256 457 603 0\n1422 -79 -25 0 1289 861 888 992 1298 935 1162 1283 1299 1337 432 1173 626 908 1288 1286 1112 1421 1405 656 738 469 415 141 119 853 616 208 858 311 1328 1346 627 88 132 246 722 302 766 880 67 253 660 177 416 587 870 1310 15 1256 919 753 941 377 166 611 256 1233 617 1007 426 156 988 670 0\n1423 -117 -25 0 992 1298 935 1280 1422 1421 1405 853 616 208 858 327 1410 1415 895 117 100 0\n1424 -25 0 1289 861 888 992 1298 1337 1299 1283 1162 935 432 1174 1326 466 1308 1286 908 1112 1267 1237 1193 1113 1263 1200 1258 302 67 766 253 1421 1405 311 656 853 1328 738 616 88 469 208 132 95 1131 415 858 141 821 93 1423 1309 589 422 115 1057 137 221 215 195 45 239 745 86 1276 988 764 670 156 320 1230 9 807 145 146 1341 0\n1425 119 359 -101 151 117 0 1113 432 1174 1308 1286 224 1303 1306 415 141 821 93 95 215 221 1268 213 601 720 512 486 778 122 1358 990 751 0\n1426 146 -101 34 -397 188 -132 133 134 216 117 375 0 908 888 1122 1132 992 1289 600 919 397 216 377 439 1323 258 1241 1099 147 772 827 1024 664 67 83 1381 607 673 443 721 13 1038 807 1425 79 195 1126 923 1134 349 205 1080 181 666 259 0\n1427 -101 34 110 -397 188 159 157 128 -132 133 134 217 117 375 0 1135 1173 466 1286 1355 1226 1365 888 992 1298 432 935 1326 1278 628 908 919 397 551 377 439 225 21 415 845 141 1197 119 484 643 1426 86 299 169 1157 634 315 778 486 873 232 1315 578 829 311 853 381 1050 434 1328 616 205 500 159 88 208 132 858 1309 589 910 379 1316 879 57 663 694 991 144 13 1425 195 355 745 239 868 746 1378 0\n1428 32 -374 24 0 1424 669 1053 1332 1107 0\n1429 -319 -132 217 240 349 375 0 1303 1173 1299 1283 1162 1295 432 466 888 1286 1337 1355 1226 919 397 551 1069 190 1319 1082 119 1016 85 772 141 138 1364 415 308 925 469 417 128 451 1259 738 192 1094 265 340 107 88 169 137 46 1055 39 1328 86 221 619 311 1099 578 1428 28 317 0\n1430 -317 139 319 305 0 466 1303 1286 1263 1355 1226 722 551 107 656 1055 578 232 486 601 634 221 86 608 0\n1431 -101 128 159 157 -132 133 134 217 396 117 375 0 432 1173 992 1295 415 141 119 643 451 151 925 1354 1364 905 644 1427 310 0\n1432 -317 319 305 24 375 0 1286 1355 1226 722 551 656 1430 578 317 232 1428 486 1099 1325 619 0\n1433 -132 133 134 217 240 396 117 375 0 1135 1337 1299 1283 1162 888 1173 1278 1286 1355 1226 1137 21 1234 919 1069 397 551 1429 722 1343 524 1432 738 469 1431 246 1414 311 589 578 138 379 232 644 364 486 310 905 634 1426 86 0\n1434 133 134 375 217 240 396 117 0 1173 1132 1433 1310 78 1414 310 589 644 138 0\n1435 -271 320 0 992 1295 1173 1337 1299 1283 1162 432 283 584 657 738 119 469 141 415 0\n1436 -101 322 359 159 152 151 117 0 432 1173 908 992 1122 1132 1300 1285 415 1425 141 195 355 119 745 239 643 868 746 1109 1146 996 987 175 0\n1437 132 159 319 -397 -164 152 150 151 134 117 354 0 628 1337 1299 1283 1162 1303 1286 1355 1267 1226 722 1272 1066 142 241 458 13 1191 764 1276 330 1436 469 738 656 1094 578 673 232 551 1244 245 850 195 639 649 0\n1438 134 217 240 396 117 375 354 0 1345 1365 1286 1355 1226 1337 1299 1283 1162 888 1298 432 935 1173 992 1326 1278 628 466 1434 819 857 272 1325 1348 873 486 778 1435 151 925 1364 644 85 310 153 1319 524 722 1437 1354 225 919 1069 905 1315 397 829 551 1432 434 232 738 159 578 469 259 311 853 381 415 1328 616 205 141 88 208 119 132 858 643 1309 589 261 910 379 1138 879 57 663 694 673 991 144 13 1425 1436 1126 355 169 181 86 147 1015 0\n1439 -322 -133 -101 34 319 117 0 1113 1173 432 1174 466 1308 1286 992 819 1348 778 1325 486 272 857 415 141 821 93 119 1240 95 1276 1383 118 112 1097 764 602 551 205 1009 1168 1358 259 147 772 1126 664 181 673 0\n1440 -133 102 -9 -101 -164 159 319 117 354 0 1113 1173 432 1174 1278 1299 628 992 589 379 879 415 141 821 93 119 643 1197 1095 95 1354 905 819 857 261 1325 1348 486 778 1439 1436 13 684 144 784 510 290 499 1403 142 97 1066 717 1272 441 765 910 764 868 1138 1358 57 195 355 1143 239 746 0\n1441 -119 322 269 159 0 908 1300 1285 1122 1132 195 355 745 239 868 746 1146 987 175 645 996 778 1109 0\n1442 119 133 102 155 196 157 117 375 0 1113 1162 1283 1299 1337 432 1174 1308 1112 466 224 1303 1289 628 888 1286 1355 1226 469 415 141 821 93 95 215 567 135 221 480 156 137 213 601 746 500 486 667 670 253 67 323 1024 359 1099 907 1195 849 919 1264 397 25 551 381 232 578 0\n1443 155 -365 -164 -134 117 375 354 0 1345 1337 1299 1283 1162 432 1173 992 908 466 1122 1132 1289 1263 1200 1258 1112 1113 1267 1237 1193 1364 1354 964 1319 722 153 524 469 1131 415 1013 141 1250 119 1088 643 1440 1442 195 1441 745 169 1276 988 86 764 258 1099 1024 67 607 253 807 670 146 156 1341 320 145 9 0\n1444 -322 -317 -295 375 78 0 1286 1355 1226 628 1424 1319 656 578 722 1276 118 121 551 1432 1430 439 232 447 1130 486 241 1325 716 819 562 0\n1445 150 112 160 109 157 354 0 1303 888 1286 1355 1267 1226 232 551 1244 245 397 195 583 649 1066 639 850 0\n1446 -143 -374 112 160 109 113 157 354 0 1303 888 1286 1263 1355 1226 1445 486 601 221 551 1244 245 397 1428 195 583 317 445 1066 639 850 0\n1447 24 -353 119 -374 120 112 160 109 113 157 0 1286 1263 1355 1226 1428 850 317 639 445 0\n1448 -31 119 -374 120 112 160 109 113 157 0 940 1286 1263 1355 1226 1424 639 1219 445 1196 317 1053 0\n1449 138 31 42 119 124 45 39 40 120 41 112 160 111 109 113 157 159 0 1286 1263 1355 1226 787 1308 671 445 472 240 322 63 1155 837 686 438 0\n1450 -139 84 -417 72 86 -150 78 77 79 0 1336 1424 168 486 1325 619 1099 1032 317 830 1053 16 971 0\n1451 -305 133 124 86 45 112 160 111 109 113 157 159 78 77 79 0 1289 1336 1303 888 1285 1300 1132 940 628 747 1305 727 1286 1263 1355 1226 1424 267 168 1445 486 1325 619 1099 1446 1024 1381 1038 67 443 601 221 865 245 397 195 583 919 1066 1116 142 746 544 241 464 716 818 802 1447 1448 1449 839 1072 104 1450 608 86 999 559 562 439 0\n1452 133 124 86 45 112 160 111 -317 159 319 78 77 79 0 1336 466 628 1424 656 578 107 1055 722 168 1451 1432 1430 447 1130 806 241 1351 716 439 562 0\n1453 217 240 78 77 79 0 1336 1345 992 1173 861 343 747 60 1415 168 267 603 1438 207 964 153 283 1319 524 151 546 925 722 1253 457 1364 1443 738 1240 656 125 119 578 996 1444 330 1094 673 1445 486 1325 619 1099 1024 766 607 880 807 611 87 204 383 279 1352 288 718 1452 819 0\n1454 -101 159 322 120 117 0 1113 432 1173 992 1174 1308 1286 95 415 141 119 821 643 93 1441 215 0\n1455 319 322 247 86 205 133 120 125 126 160 112 78 77 79 0 1337 1299 1283 1162 1173 747 1298 273 1415 1343 524 1454 469 738 1240 119 279 1352 125 288 996 718 1452 1232 807 189 465 440 1 701 211 336 0\n1456 -319 -374 160 112 109 157 240 354 0 1303 432 1173 1337 1299 1283 1162 466 1286 1263 1355 1226 1445 486 1325 819 601 221 190 1319 119 964 85 141 138 415 589 469 1414 738 1310 107 919 1069 1055 1019 1428 1446 86 317 608 0\n1457 -317 -322 319 133 112 375 78 0 466 118 107 1444 1432 1055 964 1069 1404 0\n1458 -322 319 -374 133 120 286 112 109 157 117 375 78 0 1289 466 1298 935 1337 1299 1283 1162 432 1173 1174 1308 1112 1424 1267 1237 1193 1113 1286 1263 1355 1226 1024 67 253 169 1276 118 875 86 764 551 616 208 858 1457 738 469 95 1131 415 141 119 821 685 93 988 215 670 156 320 1053 9 317 145 608 1341 828 640 0\n1459 265 113 322 212 133 112 110 117 0 880 87 398 611 315 1253 919 207 1404 0\n1460 160 112 109 157 240 78 77 79 0 1336 1296 908 1303 600 861 1337 1299 1283 1162 466 343 1453 244 767 1259 151 1415 168 267 1445 18 486 366 601 1325 20 221 619 819 1099 1024 83 766 1456 1343 524 1458 1454 469 738 107 1055 1459 204 383 1455 0\n1461 319 120 -322 112 109 157 117 375 78 0 1286 1355 1226 908 118 551 232 486 366 1325 619 819 1099 1458 0\n1462 247 72 2 171 -395 -438 -227 -160 241 79 0 1296 1162 1283 1299 1337 727 432 1301 1345 545 1335 141 415 469 1202 589 1414 539 257 767 1259 151 811 383 279 1352 114 678 88 926 1328 270 263 309 658 1118 496 996 981 42 647 172 369 609 0\n1463 -319 -160 388 241 240 396 79 0 1303 432 1174 1173 1208 190 1319 119 610 848 85 141 93 310 138 1277 1364 415 859 41 637 1003 1360 61 1462 331 0\n1464 112 109 157 240 78 77 79 0 1336 343 1286 1355 1226 1303 1320 1453 244 60 1415 168 1460 330 1463 118 1461 551 221 232 601 486 0\n1465 -150 -322 -112 241 78 77 79 0 1304 908 1296 1278 466 992 1303 1298 935 1299 1308 1174 1336 1210 1254 1288 1049 673 664 772 169 86 68 1276 764 767 1259 1017 835 1246 472 1009 203 615 500 488 268 332 1415 168 18 486 601 1325 98 810 221 619 629 616 718 1099 208 1024 612 1381 1038 731 641 1151 116 928 948 1046 623 674 1322 1264 779 429 754 1133 474 676 1127 93 35 54 1153 726 212 0\n1466 -322 109 157 240 78 77 79 0 343 1286 1355 1226 888 1173 432 1464 673 1453 244 1415 1234 1465 232 551 118 397 1319 894 85 1328 138 88 308 192 417 0\n1467 109 157 240 78 77 79 0 1296 343 1304 908 992 1337 1299 1283 1162 432 1173 466 1300 1285 1122 1132 1453 244 268 332 767 1415 1464 673 1049 203 664 743 500 615 778 1466 1094 91 738 524 469 23 415 1454 179 141 221 480 119 137 550 746 22 1109 0\n1468 157 240 78 77 79 0 343 1296 888 1298 1302 935 1336 1326 1112 1278 1137 1345 1337 1299 1283 1162 1132 432 1173 992 466 1453 244 767 1259 546 60 1415 168 267 1467 578 783 311 853 1328 1077 616 88 1346 294 208 132 662 858 1309 706 589 143 138 379 1163 457 644 85 364 310 153 1319 222 905 524 738 469 1443 415 1440 78 141 1442 1426 119 86 643 169 1441 0\n1469 -132 34 154 92 37 -308 216 273 322 109 -62 47 121 295 48 26 79 0 888 1299 1258 1286 1337 1355 1226 185 545 964 919 1323 840 397 448 315 410 216 551 634 50 772 873 349 486 1080 352 666 154 991 371 339 289 139 180 235 0\n1470 132 -146 322 240 78 77 79 0 1289 1345 1301 1296 1106 343 747 466 1305 507 1303 1173 432 1162 1283 1337 1267 1285 1300 940 1299 1288 1208 86 1157 778 1468 722 190 119 141 415 469 1165 1159 650 549 226 493 1415 1234 1319 85 138 308 417 192 341 1352 288 718 478 20 38 802 531 218 627 648 738 1094 673 1453 244 811 767 1259 151 1364 41 589 1414 88 926 263 1118 1328 309 996 1400 405 736 964 638 579 564 1247 1310 293 724 1108 819 687 183 1325 918 515 961 260 149 1372 1085 623 533 777 16 715 769 1271 0\n1471 -146 322 240 78 77 79 0 1289 1326 1301 1296 888 1303 432 1162 1283 1299 1337 1106 1173 343 747 466 1305 507 940 1468 549 722 226 493 1415 1234 1319 85 138 308 417 192 341 1352 288 718 478 20 38 802 531 218 190 119 141 415 469 738 1094 88 1328 311 578 1453 244 767 1259 151 1364 41 589 1414 926 263 1165 1309 405 736 1016 638 1171 86 90 299 1159 650 1470 874 1469 0\n1472 -132 -308 322 86 109 66 -395 -438 121 295 72 26 79 0 888 1286 1337 1355 1226 185 1278 964 919 397 448 315 551 634 772 148 873 486 764 352 154 305 371 1042 289 249 270 526 658 981 0\n1473 -308 322 240 78 77 79 0 1174 1289 1326 888 1345 1301 1296 1303 432 1162 1283 1106 1173 343 747 466 1305 1299 1337 1267 1285 1300 940 1208 1336 1468 549 722 226 493 1415 1234 1319 85 138 308 417 192 341 1352 288 718 478 20 38 802 190 119 141 415 469 738 1094 673 1453 244 811 767 1259 151 1364 41 589 1414 88 926 263 1118 1328 309 996 1400 311 578 1202 1309 405 736 60 848 310 610 93 964 1016 638 579 1171 1157 778 1472 1310 1108 819 951 687 183 1325 373 918 764 515 1247 961 724 149 1372 623 533 16 679 472 1020 725 0\n1474 132 322 240 78 77 79 0 1289 1326 1345 1301 1296 1303 432 1162 1283 1106 1173 343 747 466 1305 1299 1278 1337 1267 1285 1300 940 1208 1473 1468 549 722 226 493 1415 1234 1319 85 138 308 417 192 341 1352 288 718 478 20 38 802 190 119 141 415 469 738 1094 673 1453 244 811 767 1259 151 1364 41 589 1414 88 926 263 1118 1328 309 996 1400 1309 405 736 964 638 579 1310 1108 819 951 687 183 1325 1348 825 373 918 778 835 764 515 1246 1247 961 472 724 149 1372 623 533 16 0\n1475 -140 158 -132 86 66 -395 -438 134 72 26 79 0 185 1278 154 305 371 1042 289 249 270 526 658 981 0\n1476 322 240 78 77 79 0 1174 1336 1289 747 1345 1301 1296 343 1303 1173 432 1162 1283 1299 1106 1305 935 466 908 888 1365 1286 1337 1355 1226 1468 722 190 119 141 415 469 1453 244 811 767 1259 151 1319 85 1364 41 138 589 1414 1415 1234 308 417 192 88 926 263 1118 1328 309 996 1400 341 1352 288 718 311 578 738 107 1055 1202 405 60 848 310 610 93 964 226 493 1016 579 549 1171 168 478 20 38 802 531 208 1057 137 221 1471 1474 225 919 1069 377 397 448 315 439 551 772 873 1315 829 434 1246 472 1475 28 317 1450 1428 352 1099 764 619 373 0\n1477 -140 -132 86 66 -395 -438 134 72 26 79 0 46 1475 1371 873 0\n1478 -132 240 78 77 79 0 1174 1336 1289 747 1345 1301 1296 343 1303 1173 432 1162 1283 1299 908 888 1365 1305 935 466 1286 1337 1355 1226 1476 1276 764 169 86 1468 722 190 119 141 415 469 1453 244 811 767 1259 151 1319 85 1364 41 138 589 1414 1415 1234 308 417 192 88 926 263 1118 1328 309 996 1400 341 1352 288 718 311 578 738 107 1055 1202 405 60 848 310 610 93 964 226 493 1016 579 549 1171 225 919 377 397 448 439 551 772 1331 1367 829 802 434 531 1246 208 472 1057 137 221 1477 28 352 1450 0\n1479 240 78 77 79 0 343 1296 1303 1174 1173 1289 1337 1283 1162 1326 432 1302 1301 1345 466 1299 1278 1267 1208 1210 1254 1288 1305 747 1415 1234 1453 244 767 811 1259 151 1468 564 579 638 722 190 1319 119 610 964 85 141 93 138 405 1364 415 308 589 736 41 469 417 1414 1309 1202 192 88 523 926 1328 294 263 309 1118 996 1400 1476 169 1276 1383 764 1478 1310 1108 819 951 687 183 1325 1348 825 918 778 835 515 1199 1246 961 1120 520 472 149 1372 1357 623 533 36 54 16 429 802 74 818 1057 464 0\n1480 295 217 263 349 396 375 0 1295 1173 1289 1299 1283 1162 466 432 888 1286 1337 1355 1226 848 657 964 310 119 1016 644 141 138 405 1364 415 308 589 1057 925 469 417 1414 137 1259 1435 738 192 221 340 272 107 88 46 619 819 1055 1328 1099 1310 311 919 1069 578 397 448 1019 1428 551 772 86 317 28 0\n1481 -132 -397 -365 -164 159 319 -240 117 375 354 0 1280 1135 888 1337 1299 1283 1162 432 1173 992 1326 466 1354 905 1364 722 1256 21 281 858 919 1069 397 1432 738 469 1443 415 141 119 885 643 132 1309 1440 1442 1426 1441 86 169 0\n1482 134 132 -397 -164 159 319 117 354 0 1132 78 819 857 1325 1348 486 778 1437 0\n1483 78 77 79 0 1336 626 1280 1345 992 1299 466 1263 1285 1300 1132 267 168 1415 60 1234 1479 15 281 1256 1003 603 1480 153 283 1319 524 546 925 167 722 457 1364 637 644 310 1481 1482 1152 1443 757 738 471 107 656 1444 125 1055 578 330 1094 996 673 1445 1116 486 819 1325 0\n1484 -134 206 -295 -78 0 1280 992 273 1330 1299 709 1145 211 1003 1319 167 637 283 151 1261 87 454 789 102 207 1152 757 471 1275 611 1270 589 476 312 1214 253 670 0\n1485 132 -295 -78 354 0 273 628 1132 1280 1135 1105 1337 992 908 709 1145 211 1319 1 1277 644 753 1262 430 1261 450 454 789 570 497 386 1272 1066 142 241 683 1484 78 1310 310 246 424 1414 3 589 476 281 1256 312 858 21 253 627 670 1180 8 1059 764 337 441 377 1055 894 1404 673 0\n1486 -154 134 313 26 -78 79 0 709 1261 450 764 1033 813 371 873 0\n1487 217 69 -138 106 -447 371 149 62 90 103 96 104 95 97 77 0 1135 1288 1355 1210 1248 940 747 1342 1300 1285 1237 434 1246 472 21 941 159 627 259 7 170 876 165 280 715 718 904 648 288 1236 707 987 22 376 1146 1206 823 0\n1488 158 -9 134 -295 77 79 0 1345 888 1137 1284 1336 273 1105 1280 628 1365 1278 1096 908 1337 1283 1162 1335 1301 1330 1255 1299 992 1308 1286 589 1220 1483 709 454 789 476 1145 211 1319 1 1277 620 267 1485 919 377 1486 8 670 253 323 536 682 548 937 693 379 797 499 503 364 905 798 220 110 397 216 1069 1323 771 225 644 722 283 151 153 524 753 1262 430 1261 450 570 588 497 371 1315 1042 829 249 434 526 1246 1044 566 472 209 740 349 671 1080 1072 477 800 1020 778 1487 1256 1101 3 415 310 469 1312 738 575 622 772 1240 656 125 652 521 664 578 996 571 195 673 492 0\n1489 -9 134 -295 77 79 0 1280 1188 888 1336 908 273 1278 1105 466 1263 1200 1258 1267 1237 1193 1113 940 1337 1299 1283 1162 1483 709 1145 211 1319 1 1277 620 267 1485 919 377 1486 397 518 162 454 789 589 476 379 8 670 253 797 499 1488 873 1347 976 272 1371 146 1019 27 1103 86 790 9 145 614 1341 1363 1131 655 469 830 738 1430 0\n1490 -158 84 154 -293 319 -78 0 273 1188 908 888 466 1263 1200 1258 1278 1337 1299 1283 1162 1267 1237 1193 1113 397 377 709 1145 211 1 518 162 873 1347 976 272 1371 146 1019 27 86 790 655 623 830 1175 1430 982 738 763 469 499 1131 9 1341 145 0\n1491 302 -101 173 84 154 134 195 0 1113 432 1174 1306 415 141 821 93 95 46 1243 453 629 214 348 44 772 536 30 682 1072 671 0\n1492 288 -302 -101 173 84 154 134 -132 -78 0 1280 1284 1113 273 432 1174 1298 935 628 1161 727 908 1278 1122 1132 1308 992 415 141 821 93 709 1145 211 809 627 1261 1101 941 95 548 693 503 919 377 337 1069 753 1262 430 450 454 570 497 629 616 831 208 718 858 1180 1059 683 241 407 682 671 1072 104 800 835 778 159 247 661 147 772 565 664 808 81 0\n1493 -101 173 84 154 134 -295 -78 77 0 1345 273 1188 1336 888 1284 747 992 1286 1355 1226 908 1263 1300 1285 940 548 937 267 1485 919 397 551 709 1145 211 1319 1 518 722 153 524 386 1491 899 996 1492 464 853 746 578 232 486 366 634 1064 648 86 1055 715 1182 165 577 0\n1494 173 84 9 154 134 -295 -78 77 0 1280 273 992 888 1336 1284 1337 1299 1283 1162 1286 1355 1226 1326 1365 908 432 935 940 1319 267 1485 919 1490 397 551 771 225 722 283 151 709 1145 211 753 1262 430 1261 450 454 570 588 497 503 548 937 1493 469 738 1240 656 555 578 152 232 1309 1315 486 132 840 829 366 88 314 648 382 120 858 715 525 282 165 895 170 577 903 96 1126 384 713 824 1402 462 0\n1495 84 9 154 134 -295 -78 77 0 1280 273 1345 992 1336 888 628 1326 1337 1299 1283 1162 1365 432 343 747 1286 1355 1226 908 1278 1267 1237 1193 1308 267 1485 919 397 551 377 337 225 1319 722 283 151 153 524 709 1145 211 753 1262 430 1261 450 454 570 1041 588 497 1490 1494 323 443 1166 6 13 1038 745 426 195 152 1425 1309 1315 469 132 829 738 88 341 314 434 656 125 120 1352 858 1044 578 996 282 731 288 740 232 968 203 718 486 865 1059 673 366 634 683 446 20 86 763 807 499 1369 9 642 49 571 1266 0\n1496 -317 -448 -329 154 305 144 -295 -78 0 992 273 1188 466 1286 1355 1226 1303 1263 1200 1258 1337 940 551 709 1145 211 1319 1 518 162 722 283 151 588 107 1240 656 1430 1055 1016 555 578 830 152 232 1315 18 486 873 1347 976 601 634 1371 1374 146 221 86 27 629 1103 1228 790 614 881 891 0\n1497 -100 146 155 -329 0 940 787 861 1103 1018 1389 614 173 325 740 499 571 47 642 0\n1498 -312 87 73 155 98 -329 154 134 305 133 79 0 1113 1162 1283 1299 1337 432 1174 1303 1308 1286 1302 1379 1336 469 415 141 821 93 1197 95 551 601 1325 634 221 86 1177 881 1497 640 807 1203 1230 786 1046 703 1151 1077 282 294 780 0\n1499 134 -295 77 79 0 992 273 908 1336 888 787 1278 1365 1337 1299 1283 1162 1113 432 1174 1211 1355 1226 1308 1286 267 1483 1485 919 397 551 377 225 709 1145 211 1319 1 1277 620 722 283 546 1261 386 1486 1489 1495 472 1363 63 1246 755 434 835 829 1017 673 1496 738 469 95 415 141 1197 1101 821 603 925 93 457 1354 1250 890 905 188 939 1498 486 199 232 778 578 1207 381 147 881 136 205 928 181 333 259 651 695 0\n1500 -295 77 79 0 1336 1280 273 992 1330 1299 1278 1365 628 1288 1308 1286 1483 709 1145 211 1003 1261 87 454 789 570 588 267 283 1319 151 167 637 1485 225 1499 102 207 1152 757 471 933 483 1275 611 1270 220 589 910 476 1315 379 1138 1214 829 879 670 434 57 253 1246 1143 323 472 276 355 359 1269 567 907 0\n1501 -9 -447 -132 84 77 79 0 273 908 1173 1278 1280 1105 1337 1135 628 1284 919 377 771 1500 964 1483 709 1145 211 753 1262 430 1261 450 454 789 570 497 589 910 476 138 379 620 85 879 1486 281 1256 8 858 21 941 670 1138 627 253 57 1333 323 663 170 548 1236 165 937 648 715 0\n1502 -403 149 371 147 84 113 342 77 0 1337 940 663 1236 648 715 165 577 1148 1324 650 1159 0\n1503 149 88 102 173 9 -447 147 -132 84 101 134 -239 97 133 77 0 273 1162 1283 1299 1337 466 1280 1290 1278 934 1306 1284 1307 1296 1336 1254 1288 1342 727 747 432 1096 1345 888 940 1121 1281 1279 454 570 1138 548 937 693 503 771 469 738 107 1055 1165 1145 211 753 1262 430 1261 450 1502 57 879 231 379 585 682 44 197 864 418 291 767 501 1259 202 151 1164 376 707 114 288 678 345 88 477 1328 120 89 309 311 282 996 578 903 1416 96 384 713 939 577 1119 1117 1198 808 0\n1504 88 102 173 9 -447 147 -132 84 101 134 -239 97 133 77 0 1280 273 1284 908 747 548 937 434 408 1246 771 1145 211 753 1262 430 1261 450 454 570 1503 868 745 363 1264 854 389 402 1352 282 288 903 718 170 966 165 1129 715 0\n1505 -88 173 128 98 106 147 84 77 79 0 1174 1295 1173 432 1162 1283 1299 1337 1284 1210 1254 1288 935 1096 1308 1286 1336 908 1211 1122 1285 1300 1132 548 359 1500 657 119 141 415 469 1202 610 93 964 1483 709 1262 430 386 704 826 846 895 223 525 768 907 382 995 24 556 567 366 1321 229 1134 745 1398 199 751 205 868 520 778 84 0\n1506 -102 9 267 -293 84 77 79 0 1280 1174 1295 1173 432 1162 1283 1299 1337 908 940 935 1305 1326 1500 448 772 377 657 119 141 415 469 1202 610 93 964 1483 709 1262 430 1261 454 497 858 586 208 314 74 160 531 132 429 1018 802 1309 1375 528 726 1486 1079 0\n1507 173 -447 -132 84 77 79 0 1295 1173 432 1096 919 1483 709 1261 434 1044 1501 1506 1414 463 633 755 209 1500 448 772 657 119 141 415 964 497 386 1505 1504 0\n1508 -447 -132 84 77 79 0 1280 273 1295 908 628 1173 1326 432 1314 1255 1221 1330 1500 919 448 50 377 337 657 119 141 415 1483 709 1145 211 753 1262 430 1261 450 454 570 1041 497 434 1044 1501 1506 1507 323 357 1166 6 139 1038 426 235 152 1309 132 88 120 282 968 1059 1136 1329 658 289 94 0\n1509 9 -132 84 77 79 0 1280 1295 1173 432 273 908 1188 888 1096 1365 727 628 1306 1326 1508 829 902 104 1072 671 682 274 1483 709 1145 919 397 72 770 477 618 350 720 377 337 1212 683 1059 211 298 1500 657 119 141 415 753 1262 430 1261 450 454 789 570 497 1506 968 282 1014 1151 872 1046 132 1230 1309 807 152 409 952 426 670 988 0\n1510 -132 84 77 79 0 273 1295 1173 432 1162 1283 1299 466 908 888 1365 727 1188 628 1096 1306 1337 1286 1500 657 119 141 415 469 738 107 1055 1016 1483 709 1145 211 225 919 377 397 448 551 772 1508 829 902 104 1072 671 682 72 274 770 1212 477 298 982 618 209 1175 350 623 1157 720 1397 86 221 1509 220 1327 1158 578 205 381 0\n1511 132 -317 134 -78 354 0 1280 466 908 628 1105 1337 107 1055 709 454 789 386 1272 1310 1404 1066 1414 673 142 589 476 203 241 312 12 253 764 670 8 0\n1512 -9 77 79 0 908 888 1208 1295 432 1162 1283 1299 1336 1173 1278 1280 1105 628 1337 1284 940 267 1483 1500 964 657 119 141 415 469 738 1511 1510 472 1246 835 1273 20 504 89 919 448 772 397 551 377 1323 709 454 789 570 589 910 476 138 379 620 85 879 1486 281 8 858 670 1138 253 57 323 1148 548 577 693 557 0\n1513 149 154 402 142 147 138 274 342 134 133 0 1337 1345 992 1278 432 1355 1226 727 1055 1416 1148 179 996 57 309 675 899 879 1328 806 46 379 88 238 678 987 114 0\n1514 -154 9 313 -78 0 1330 1299 709 1261 87 764 1033 813 1270 256 611 0\n1515 149 154 286 89 147 143 138 36 274 342 134 384 133 0 1105 1337 628 1284 935 940 20 8 670 253 323 548 693 382 557 525 577 509 1513 0\n1516 -308 109 117 154 -448 147 -293 144 274 121 151 0 888 1286 1337 397 551 111 634 128 486 151 921 0\n1517 77 79 0 1336 1280 1295 1173 1299 1283 1162 466 908 1208 1278 1365 1326 432 1302 888 1337 1304 267 1483 386 588 709 454 789 1500 657 964 119 1016 141 415 469 1165 738 107 1055 1511 225 919 1323 1510 377 397 448 472 839 551 772 504 1246 89 434 835 829 1273 1512 1414 1514 1515 480 868 426 152 1309 132 88 523 1328 120 294 311 282 578 1516 86 1235 1327 433 151 1249 1259 949 1092 332 0\n1518 9 -78 132 0 273 1330 992 1299 709 1145 211 1003 1261 87 386 1414 1310 102 207 1152 964 1270 283 1319 611 151 167 1275 637 471 757 0\n1519 134 294 112 133 132 0 1310 1404 246 1055 703 0\n1520 -147 -78 -77 0 1278 1280 1330 1299 466 992 134 1518 732 476 117 100 509 589 379 879 57 1143 471 220 709 1261 87 386 772 287 664 1139 673 611 256 272 1519 207 964 1253 283 151 0\n1521 -78 -77 0 1280 1278 466 992 940 1337 1299 1283 1162 117 100 509 134 1518 220 589 476 732 379 879 57 1143 746 137 221 1520 1148 764 441 1276 1055 1324 86 1159 1157 650 1100 1165 524 469 1454 0\n1522 -403 142 149 117 147 -154 0 992 466 940 1337 1299 1283 1162 764 441 1055 1276 1143 1324 746 86 1159 137 1157 650 221 1100 1165 524 469 1454 0\n1523 142 149 117 147 -154 79 0 1280 1290 1278 934 1306 1326 1307 1336 1254 1288 1300 1285 940 1345 466 747 1305 1308 1286 1174 432 1337 1299 1283 1162 1234 764 1276 751 1517 117 100 509 456 1522 57 879 231 379 585 1239 682 308 589 44 197 693 417 1309 418 291 192 1238 811 501 88 1146 1153 1328 676 746 544 309 137 464 239 996 221 818 195 802 215 93 821 141 415 469 738 1400 1094 124 81 155 505 248 565 1318 808 661 0\n1524 -156 -197 -142 117 -154 79 0 1345 1290 1306 934 1297 1326 343 940 466 747 1308 1286 1305 1174 432 1337 1299 1283 1162 1517 732 1309 132 341 449 1238 585 595 886 1153 44 418 811 1239 693 231 682 88 1328 309 996 697 355 764 1276 751 456 676 746 544 137 464 221 818 215 802 93 821 141 415 469 738 1400 1094 124 81 155 505 565 1318 808 661 0\n1525 -155 135 80 18 31 111 11 -154 79 0 787 1174 1210 1254 1288 764 1276 751 1517 117 334 1340 430 1362 89 456 1202 738 1400 1240 1094 610 81 93 404 155 505 565 1318 808 661 0\n1526 -197 -142 149 117 -154 79 0 343 1326 1345 1290 934 1297 1337 1299 1283 1162 1113 432 1173 992 1174 1308 1286 1306 1517 732 1309 132 88 1328 309 996 341 449 1238 697 355 22 764 1276 330 134 231 585 1239 682 44 595 693 418 886 811 1153 1524 1525 469 95 415 141 119 821 17 643 93 524 694 215 673 221 1380 720 778 0\n1527 155 -142 117 -154 -77 0 1280 787 1302 1326 1337 1299 1283 1162 1113 432 1173 1306 992 1174 1295 1308 1286 1263 1365 117 732 1309 132 88 127 389 1328 1213 523 294 334 344 570 1414 355 764 1276 330 751 1340 430 1362 89 378 100 895 513 134 70 469 95 415 141 269 119 821 505 17 643 617 93 524 451 873 215 1245 151 1268 857 920 1315 829 0\n1528 -55 -155 111 100 79 0 787 1174 343 1210 1254 1288 738 1240 610 93 1202 1517 117 334 1340 430 1362 89 1118 941 244 1256 811 414 1400 505 404 0\n1529 149 117 147 -154 79 0 1326 432 1345 1137 940 1301 992 764 1276 441 751 1517 134 117 1523 732 1414 1309 132 88 926 1328 127 309 674 996 1526 364 890 928 1527 1165 738 650 1094 1159 673 68 631 1528 263 151 283 39 964 819 1519 0\n1530 -271 112 274 132 0 992 283 39 964 819 1519 0\n1531 -142 117 147 -154 79 0 992 1326 940 432 1345 1301 764 1276 441 751 1517 134 117 732 1527 1414 1309 1165 738 132 650 1094 88 1159 673 926 1328 127 309 674 996 1528 1530 151 263 41 631 1354 68 890 928 0\n1532 -155 110 117 147 -154 79 0 1280 992 940 1337 1290 1278 934 1306 1307 1336 1254 1288 432 1345 1301 844 1531 1234 764 441 1055 751 1517 117 100 509 1165 650 1159 1324 57 879 231 379 585 1239 682 308 589 44 197 693 417 1414 418 291 192 811 501 88 1153 926 1328 127 309 674 996 1528 1525 263 503 631 630 68 890 928 0\n1533 -101 119 120 117 0 1113 1308 1286 432 1174 95 415 215 141 93 821 0\n1534 117 147 -154 79 0 992 908 1337 1299 1283 1162 764 1276 441 1517 134 1529 480 868 745 195 1533 469 738 1532 1094 151 673 1530 0\n1535 -317 289 -316 132 0 1276 12 1094 222 14 673 964 819 1519 0\n1536 133 112 -117 -316 79 0 1280 992 1342 727 935 1306 1162 1283 1337 432 1173 1303 1263 1285 1300 1132 940 1299 747 1305 1379 1517 134 152 1213 1535 738 469 415 141 119 190 167 17 524 114 1352 680 1020 707 376 220 1414 1186 1276 330 441 1055 1521 117 100 895 1362 1404 34 1152 471 746 823 544 757 464 1164 637 818 570 1003 802 1373 194 705 817 651 505 1353 0\n1537 -133 -117 -154 -77 0 787 1162 1283 1299 1337 432 1173 1306 466 1267 1285 1300 940 747 1215 134 764 152 1213 1535 738 469 415 141 119 17 524 220 1414 1276 330 514 117 334 1340 961 430 1108 819 272 1325 1348 14 760 486 918 778 500 746 515 1150 293 868 724 1089 360 1038 493 236 541 1076 0\n1538 -117 -154 79 0 1337 1283 1162 432 1173 1306 1303 1263 1285 1300 1132 1299 992 764 1276 330 514 1517 117 1362 134 152 220 1213 1414 1535 738 469 415 141 119 17 190 524 167 1537 1310 34 1536 1152 471 673 113 757 664 200 637 50 235 1003 896 705 0\n1539 155 159 117 -154 -77 0 992 1337 1299 1283 1162 466 1306 1300 1285 1122 1132 764 1276 441 469 1527 1454 221 480 137 720 882 746 778 1146 1109 987 996 175 0\n1540 -154 79 0 1280 787 992 940 1174 1210 1254 1288 343 1330 1299 1278 1263 1517 117 334 1340 430 1362 89 100 509 134 751 764 441 1055 1538 1534 772 881 287 1160 664 524 673 1530 151 1539 1165 1202 738 650 1240 1159 610 93 404 383 1347 204 1253 87 611 1270 1139 589 732 471 379 1110 879 57 0\n1541 -133 -149 110 117 258 0 940 747 466 1298 1215 1330 1314 868 360 493 724 293 1340 430 877 32 1108 819 857 272 1325 873 486 1252 541 1059 1076 189 236 807 1038 1217 0\n1542 133 112 142 111 156 159 113 132 0 1263 1285 1300 1132 466 1182 1116 86 330 169 0\n1543 112 142 111 156 159 117 274 -77 0 787 1300 1285 1122 1132 1055 117 334 134 1530 151 1542 819 1541 1348 1109 778 0\n1544 142 111 156 159 117 274 -77 0 787 1263 1300 1285 1122 1132 1055 117 334 1543 673 111 86 1182 819 1348 39 778 151 1109 1541 0\n1545 -112 234 79 0 787 908 992 1278 1299 1258 1517 117 127 674 1328 1540 334 488 673 1049 203 664 500 698 772 1051 982 928 763 700 499 0\n1546 134 110 112 128 111 117 79 0 787 1337 1267 1285 1300 1540 1517 117 334 134 1310 819 1541 1348 1247 778 0\n1547 111 156 159 117 -155 79 0 466 787 1326 432 1299 845 1517 117 1362 334 1340 1401 1360 738 107 134 1544 732 1414 1309 132 88 1545 1530 151 1546 1152 964 483 1319 757 167 637 0\n1548 -272 117 -317 79 0 787 466 1345 432 1326 1122 1285 1300 1132 107 1540 1517 117 334 134 125 309 1334 153 1160 246 1328 205 964 772 88 1310 132 819 1309 1348 39 14 732 778 151 500 84 1541 0\n1549 134 128 110 -9 111 117 79 0 787 1278 1280 1337 992 1517 117 100 509 589 379 879 57 732 1540 334 134 1310 1546 1541 673 1148 664 772 0\n1550 -134 110 408 47 117 0 1330 1299 102 207 1139 1253 611 0\n1551 271 -234 -156 117 -155 79 0 787 747 1298 507 1173 432 1326 1288 1365 466 88 132 1309 738 1240 119 141 1011 450 87 746 464 616 218 627 471 1548 996 107 1055 1517 117 1362 334 1340 1401 430 89 378 513 134 70 151 1550 1549 424 7 829 902 1017 673 1404 819 857 272 1315 873 0\n1552 -234 -156 117 -155 79 0 1280 466 432 1326 1278 992 1337 738 107 1055 1517 117 100 509 134 88 132 1309 589 732 379 879 57 1551 1530 673 664 111 772 86 1324 0\n1553 134 110 112 111 117 113 79 0 787 1337 1267 1285 1300 1540 1517 117 334 134 1404 819 1541 1348 1247 778 0\n1554 -156 117 -155 79 0 787 466 738 1548 996 107 1055 1517 117 1362 334 1340 1401 845 134 471 823 1552 1545 1530 151 1553 43 1550 489 0\n1555 271 117 -155 79 0 787 466 1173 1345 432 1365 1326 1288 738 1548 996 1554 1547 524 153 964 1240 119 141 107 1055 1517 117 1362 334 1340 1401 430 89 378 70 151 1553 673 1545 1017 88 1346 1011 902 132 627 450 829 1309 7 1549 424 0\n1556 117 -155 79 0 466 1345 1337 1122 1285 1300 1132 738 107 1055 1517 134 1548 996 1554 1547 524 153 1160 964 772 1555 39 1530 819 673 1310 111 1414 86 732 1115 0\n1557 -155 79 0 1280 1173 432 727 1342 466 1278 1267 1285 1300 1132 1330 1299 1540 1517 117 100 895 134 738 1240 119 141 1556 152 220 1186 114 1213 555 1414 707 1328 964 1310 376 1011 819 87 272 1348 14 256 398 778 500 611 249 55 1270 139 572 287 1164 264 858 235 387 896 0\n1558 134 -117 79 0 1113 1162 1283 1299 1337 432 1174 1308 1286 1267 1285 1300 1132 908 220 1414 152 1213 1557 469 415 141 821 93 95 1540 1517 134 1310 819 1325 1348 14 486 778 500 1222 55 195 868 745 0\n1559 -117 79 0 787 1280 1283 1299 1337 432 1173 992 1295 727 1342 1302 1301 343 1304 1162 1557 469 415 141 119 643 451 151 1197 484 1517 117 100 895 334 456 152 220 1128 1186 114 1213 1414 707 1077 376 294 1558 1013 263 1118 941 244 1256 1101 266 316 295 268 811 1043 414 1070 695 282 900 332 383 505 1018 651 372 1144 433 1067 23 1428 500 1099 14 619 0\n1560 294 128 -134 79 0 1306 1162 1283 1299 1337 432 1173 992 1295 466 1559 1557 469 415 141 119 643 451 151 17 524 1240 1517 117 819 51 221 1454 1533 169 1383 112 355 86 692 205 1313 87 471 1550 0\n1561 265 128 -134 79 0 787 1306 1162 1283 1299 1337 432 1173 992 1295 466 1135 1288 1365 1263 1285 1300 1132 1560 272 207 43 1559 1557 469 415 141 119 643 451 151 17 524 1517 117 334 1340 430 1362 89 378 513 134 70 87 53 1101 1550 753 809 941 471 483 627 7 829 902 1315 1097 857 330 34 0\n1562 128 -134 79 0 787 1113 992 1174 1162 1283 1299 1337 432 1173 1306 600 1559 1557 469 415 141 119 17 524 821 93 643 95 1540 1517 117 334 1340 134 1560 1325 1348 486 804 778 83 1024 1561 1261 692 900 1383 1099 1441 1195 1358 857 0\n1563 -120 -403 142 0 466 221 480 137 1143 746 0\n1564 -134 79 0 1280 1306 1162 1283 1299 1337 432 1173 1303 1278 466 1263 1314 940 1559 1557 469 415 141 119 190 722 17 524 1240 1517 117 100 509 1170 1152 1562 1414 589 732 379 879 851 57 1236 1563 1454 169 1383 112 875 86 997 205 629 328 753 563 544 0\n1565 -322 79 0 787 1162 1283 1299 1337 432 1173 1295 466 1278 1113 1263 1200 1258 1557 469 415 141 119 657 1131 1540 1517 117 334 169 1276 1383 86 121 740 982 763 499 325 145 1395 1341 571 146 642 807 1369 0\n1566 79 0 1337 1299 1283 1162 1113 432 1173 992 1174 1303 1306 1267 1308 1286 1517 134 1540 1557 469 95 415 141 119 821 17 643 93 524 1559 1564 1565 1441 1454 221 601 720 486 778 1222 0\n1567 -134 0 1566 177 0\n1568 -158 0 1566 416 0\n1569 -49 0 1566 502 0\n1570 240 0 1566 587 0\n1571 -104 0 1566 870 0\n1572 -264 0 1570 626 15 0\n1573 -263 0 1570 1280 281 0\n1574 -217 0 1570 1256 0\n1575 233 0 1570 1257 0\n1576 -103 0 1572 753 0\n1577 -363 0 1573 612 0\n1578 -102 0 1573 858 0\n1579 -216 0 1574 1135 21 0\n1580 -55 0 1574 941 0\n1581 -54 0 1579 627 0\n1582 -408 0 1581 1580 1576 1578 1571 1274 0\n1583 313 359 -316 119 -101 0 1582 1330 1569 1299 439 813 1425 256 220 611 1270 0\n1584 9 132 0 1330 1569 1299 1567 1582 466 1414 1270 1310 611 819 256 272 0\n1585 -154 119 155 37 0 1306 1303 1162 1283 1299 1337 432 1173 1295 1574 992 908 1336 1578 469 415 141 119 643 451 925 1354 190 722 17 524 1197 1095 764 1071 441 717 97 1403 13 1583 377 919 1584 220 1539 1425 588 857 168 1442 0\n1586 117 -100 -101 322 0 1306 432 1173 992 1295 1568 1582 1330 1569 1299 415 141 119 643 451 151 17 524 1253 1454 611 186 1139 0\n1587 9 322 0 1330 1569 1299 1582 1270 1584 611 919 256 315 0\n1588 294 293 132 0 1567 819 1519 1310 673 246 894 0\n1589 -113 271 119 117 0 466 1337 1299 1283 1162 883 1055 684 107 677 738 439 469 1425 0\n1590 133 113 293 132 0 1567 1310 1404 246 673 894 0\n1591 155 119 -214 322 0 861 1337 1299 1283 1162 1369 807 47 499 1587 220 469 1585 1586 640 0\n1592 -100 -155 37 -9 0 1284 861 1566 1577 466 1424 738 107 717 589 1220 892 1133 754 779 1322 491 1037 554 351 1076 659 1018 1034 1260 73 1095 97 0\n1593 293 132 267 322 0 1566 861 1295 1263 1200 1258 940 1286 1355 1267 1226 1335 1301 1330 1255 1299 321 1369 807 47 499 10 740 571 1587 892 330 561 195 1588 1325 1348 486 778 1591 1165 738 1094 673 1592 146 764 650 12 1100 1073 1159 1050 672 524 722 325 578 996 1380 232 649 319 847 5 1244 639 652 0\n1594 119 271 143 132 -214 322 0 861 1263 1200 1258 1567 888 1286 1355 1226 1369 807 47 499 1587 220 1591 1589 738 1592 1094 146 673 764 1404 1535 819 311 1325 578 486 1073 232 722 0\n1595 132 267 322 0 1278 1137 1299 1566 1577 888 908 1300 1285 1578 1288 321 1587 892 1133 754 779 1322 131 198 589 379 364 890 879 110 1593 397 315 551 1435 1594 195 1126 355 613 704 1022 1134 745 136 868 928 1143 1146 333 57 598 299 1138 135 490 261 1311 370 930 0\n1596 -119 -132 -9 0 1278 1137 1299 1566 1577 888 908 1300 1285 1578 1288 919 397 551 910 892 1133 754 779 1322 131 198 589 379 364 890 879 110 195 1126 355 613 1022 1134 745 136 868 928 1143 1146 333 57 598 299 1138 135 490 261 1311 370 930 0\n1597 -375 120 65 391 84 88 77 -9 0 1278 1566 1577 1336 1280 1578 628 1210 1254 1288 892 1133 754 779 1322 659 589 379 879 900 168 454 476 570 1138 733 57 443 1143 323 276 359 223 907 0\n1598 267 322 0 1137 1299 1278 1566 1577 861 888 1208 1308 1286 1263 1200 1258 1587 589 892 1133 754 779 1322 422 1024 379 860 526 198 364 905 798 220 321 47 1369 499 807 1595 134 919 1323 1069 910 397 566 216 349 1080 504 472 1596 567 1591 738 1592 1240 146 764 58 750 221 1597 1432 1099 1319 619 373 0\n1599 -132 322 0 1572 1575 787 1570 1571 1288 1576 1580 1581 908 1365 1568 1598 173 367 378 606 430 298 89 1587 220 110 225 771 919 7 377 315 829 439 1435 1315 151 0\n1600 -293 322 0 1572 1575 787 1570 908 628 1336 1571 1288 1576 1580 1581 1568 1365 1599 1272 1598 173 367 378 606 430 298 89 1587 220 110 377 315 439 982 1435 241 151 142 1066 267 70 513 7 1315 829 0\n1601 -133 322 0 1566 787 1570 1573 1278 466 1568 1336 628 1599 1600 1588 272 1435 151 1272 1587 589 379 879 1598 82 509 57 173 367 877 892 220 857 1541 1252 1143 1059 732 683 267 241 1066 142 0\n1602 322 0 1295 466 1587 220 1599 1600 561 1588 272 1435 1601 195 1589 1590 0\n1603 -308 0 1602 466 169 0\n1604 -316 0 1602 1276 0\n1605 -267 0 1602 1383 0\n1606 -146 0 1603 86 0\n1607 -154 0 1604 764 0\n1608 -106 0 1605 209 0\n1609 -186 293 0 1295 1602 1173 432 1162 1283 1299 1337 466 1582 861 628 1263 1607 1200 1258 919 1588 272 256 611 880 766 561 581 119 141 415 469 1584 241 174 242 499 807 1592 146 0\n1610 293 117 0 1295 466 1566 1278 1280 787 1336 583 919 561 1588 1584 195 272 589 892 1435 379 151 1589 879 1590 1609 142 284 1066 100 334 267 509 1541 732 57 1143 0\n1611 -77 110 62 117 0 908 787 1568 1365 1571 1288 1576 1580 1581 1610 377 439 70 117 513 334 1362 1315 378 1340 89 829 430 7 0\n1612 -89 84 88 77 -9 31 0 1566 1278 1096 1121 747 1300 1285 1578 671 589 379 879 892 89 170 945 876 477 165 1271 59 832 715 140 648 1048 1236 288 22 663 987 57 1146 1138 572 0\n1613 96 89 -447 -132 -9 427 0 1137 1566 1577 1278 1571 1580 1288 1581 1576 1323 771 589 379 892 1133 754 779 860 526 364 905 798 110 7 164 481 349 566 0\n1614 110 -9 186 117 0 908 888 1161 1566 1577 1284 861 1336 1568 1365 1574 1208 1579 1578 1608 1606 892 1133 754 779 554 351 440 110 407 682 142 1610 397 216 377 439 1611 267 1066 1272 225 910 1315 829 434 1246 159 472 259 1612 1613 36 430 1021 149 1262 1372 842 623 709 533 484 436 1399 701 1156 0\n1615 -9 186 117 0 908 1566 1577 466 1295 1567 1336 1299 1610 377 589 892 1133 754 779 1322 422 1024 1614 151 534 1435 275 272 512 619 819 51 1099 1310 1046 134 1151 168 71 884 122 684 0\n1616 9 117 0 1326 1330 1569 1299 1582 343 1568 1570 466 1345 888 1295 992 1296 432 1567 1122 1285 1300 1132 1286 1606 1337 1355 1226 1308 1297 1608 1610 397 551 1309 1270 132 1238 611 88 341 256 1253 1328 99 449 1352 272 1371 151 309 311 703 415 819 51 46 346 283 1259 996 578 1055 221 1016 448 767 772 418 1115 28 995 830 886 1397 511 0\n1617 117 0 1566 628 1577 1263 1607 1200 1258 1267 1606 1237 1193 1337 1299 1283 1162 940 1616 589 892 1615 1133 241 76 754 312 779 742 1322 807 862 146 499 9 1592 1205 469 460 1183 0\n1618 278 0 1617 152 0\n1619 -9 0 1617 220 0\n1620 -73 0 1617 1128 0\n1621 -81 0 1617 1186 0\n1622 -62 0 1617 1090 0\n1623 -47 0 1617 1566 866 0\n1624 -297 0 1618 727 114 0\n1625 -289 0 1618 1213 0\n1626 -128 0 1619 1414 0\n1627 -407 0 1619 1299 1569 1330 1270 0\n1628 132 0 1619 1584 0\n1629 -362 0 1623 1299 198 0\n1630 -424 0 1624 707 0\n1631 -136 0 1624 987 0\n1632 409 0 1627 1582 611 0\n1633 293 0 1628 919 0\n1634 364 0 1629 1577 754 0\n1635 423 0 1630 1342 376 0\n1636 320 0 1632 256 0\n1637 -313 0 1633 908 377 0\n1638 -305 0 1633 888 397 0\n1639 -303 0 1633 1625 625 0\n1640 156 0 1634 1133 0\n1641 318 0 1634 898 0\n1642 -294 0 1636 466 272 0\n1643 -302 0 1636 1371 0\n1644 -311 0 1637 1618 426 0\n1645 -143 0 1638 551 0\n1646 -141 0 1639 205 0\n1647 -66 0 1640 474 0\n1648 -121 0 1640 676 0\n1649 -281 0 1641 466 137 0\n1650 -133 0 1642 819 0\n1651 -140 0 1643 46 0\n1652 -149 0 1644 868 0\n1653 -120 0 1649 221 0\n1654 -271 0 992 1637 1295 1633 1296 1651 1607 1631 1626 1567 1652 1646 1285 1300 432 1174 1647 1622 1288 1578 1621 1635 283 1259 275 657 448 635 767 500 610 772 193 418 93 276 826 995 277 1164 490 0\n1655 -110 0 1654 151 0\n1656 164 0 1654 1574 925 0\n1657 2 0 1655 1301 1620 1580 1626 263 0\n1658 -196 0 1656 1354 0\n1659 -155 0 1657 1566 529 0\n1660 -87 0 1657 1628 939 0\n1661 -34 0 1658 905 0\n1662 101 0 1659 1162 1283 1299 1337 469 0\n1663 262 0 1662 415 0\n1664 -227 0 1663 432 141 0\n1665 -219 0 1663 1605 602 0\n1666 -438 0 1664 821 0\n1667 -57 0 1665 259 0\n1668 439 0 1666 1174 93 0\n1669 147 0 1668 1286 1308 1653 1648 1645 1567 1650 1606 1177 0\n1670 309 0 1669 772 0\n1671 -4 0 1669 1662 147 0\n1672 -273 0 1670 992 664 0\n1673 112 0 1671 1646 1660 1661 1667 181 0\n1674 0 1673 1672 673 0\n"

theorem raw_n8_b7_p0010 (word:Fin 8→Fin 3) (base val:Sat.Valuation)
 (h:ModuleOPG1808CNF.LexModel word (lexRot 8) lexPerm base)
 (heq:∀ i,i<OPG1808Cuts.selectorBase 8→(val i↔base i))
 (hc:OPG1808Cuts.CutModel (n:=8) 7 val)
 (hp:word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(0:Fin 3)∧True):False:=by
 have m:=h.toModel
 have bad:=cert_n8_b7_p0010 (val 1) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 81) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 145) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 247) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 267) (val 268) (val 269) (val 270) (val 271) (val 273) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 337) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 384) (val 503) (val 504) (val 510) (val 511) (val 573) (val 574) (val 587) (val 588) (val 589) (val 590) (val 594) (val 595) (val 596) (val 597) (val 601) (val 602) (val 608) (val 609) (val 615) (val 616) (val 678) (val 679) (val 716) (val 717) (val 718) (val 719) (val 720) (val 721) (val 722) (val 723) (val 724) (val 728) (val 729) (val 730) (val 731) (val 732) (val 733) (val 734) (val 735) (val 736) (val 737) (val 738) (val 739) (val 740) (val 741) (val 742) (val 743) (val 744) (val 745) (val 746) (val 747) (val 748) (val 749) (val 750) (val 751) (val 752) (val 753) (val 754) (val 755) (val 756) (val 757) (val 758) (val 759) (val 760) (val 764) (val 765) (val 766) (val 767) (val 768) (val 769) (val 770) (val 771) (val 772) (val 773) (val 774) (val 775) (val 776) (val 777) (val 778) (val 779) (val 780) (val 781) (val 782) (val 783) (val 784) (val 785) (val 786) (val 787) (val 788) (val 789) (val 790) (val 791) (val 792) (val 793) (val 794) (val 795) (val 796) (val 797) (val 798) (val 799) (val 800) (val 801) (val 802) (val 803) (val 804) (val 805) (val 806) (val 807) (val 808) (val 809) (val 810) (val 811) (val 812) (val 813) (val 814) (val 818) (val 819) (val 820) (val 821) (val 822) (val 823) (val 824) (val 825) (val 826) (val 827) (val 828) (val 829) (val 830) (val 831) (val 832)
 exact (Or.elim bad
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 6 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 1 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 25) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 1 2 (hp.2.2.1)) (by decide)) (b))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
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
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 2 0 0) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 1) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 0 2 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 17 1 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 0 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 3 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 1) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 0) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 3 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 4) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 3 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 1 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 31 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 6 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 18 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 18 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 4 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 30 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 3 (hp.2.2.2.1)) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 0 3 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 1 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 1 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 7 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 5 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 0) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 1 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 5) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 4 6 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 7 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 29 3 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 6) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 4 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 1) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 0 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 3) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 31 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 6 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 1 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 3) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 0 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 1) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 2 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 0 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 2) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 0) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 17 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 6) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 5) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 1 (by decide) 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 33 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 3) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 6) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 32 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 6) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 7) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 1 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 0 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 5) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 7) (by decide)) (b))
 (fun b=>(hc.reach_clause 1 (by decide) 0 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 2) (by decide)) (b.1) (b.2))))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 42 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 21) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 0 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 2) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 29 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 26) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 33 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 2) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 1 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 27 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 2) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 2) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 2) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 17 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 2 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 0 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 6) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 6 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 6) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 2 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 33 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 26) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 2) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 2) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 7 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 3) (by decide)) (b))
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 17 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 4) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 0 (by decide) 7) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 22) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 42 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 4) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 1 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 42 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 30 3 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 7) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 0) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 6) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 1 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 1 (by decide)) (by decide)) (b.1) (b.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 2 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 3 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 0) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 2) (b.1) (b.2))
 (fun b=>(hc.reach_clause 2 (by decide) 1 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 6) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 1) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 6 1) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 2) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 1) (by decide)) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 30 3 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 3 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
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
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 1 (hp.2.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 7) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 18 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 4 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 1 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 31 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 4 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 3 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 2 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 27 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 29 3 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 6 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))))))
end OPG1808CutCertificates
end

end Cut8Prefix0010CompactV3Packet

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
    (hprefix3 : color (3:Fin 8) (finRotate 8 (3:Fin 8)) = (0:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  exact Cut8Prefix0010CompactV3Packet.OPG1808PhysicalPrefix.predecessor_reachable_of_cut_exclusion
    (fun word ↦ word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(0:Fin 3)∧True) Cut8Prefix0010CompactV3Packet.OPG1808CutCertificates.raw_n8_b7_p0010
    D color htournament hnoRainbow hcycle hminimal ⟨hprefix0,hprefix1,hprefix2,hprefix3,True.intro⟩
