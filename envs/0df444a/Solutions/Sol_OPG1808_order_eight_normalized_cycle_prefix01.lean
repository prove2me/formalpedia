-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix01
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:26:47.840649+00:00
-- url     : https://prove2.me/submissions/eea845a7-b8a0-4fb4-922d-611c24c335af

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

namespace Cut8Prefix01Packet

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
lrat_proof cert_n8_b7_p01
 "p cnf 833 989\n-825 236 0\n-317 -294 318 0\n199 263 327 0\n-353 -323 355 0\n-38 -111 -181 0\n243 307 371 0\n47 54 111 118 175 182 0\n-833 382 0\n-149 -40 -123 0\n-380 -349 381 0\n-288 -315 283 0\n-336 -381 333 0\n-151 -179 0\n-731 176 184 0\n-13 -98 0\n-363 -341 365 0\n-632 -157 -75 0\n-150 342 0\n-6 -112 -185 0\n-170 362 0\n-687 -148 -75 0\n777 778 779 0\n235 299 363 0\n234 298 362 0\n-818 148 149 150 151 152 145 0\n-308 -285 309 0\n2 66 130 0\n-358 -368 360 0\n-2 -140 -89 0\n-38 -175 -117 0\n-332 -350 334 0\n-52 -159 0\n-2 -75 -145 0\n-87 -115 0\n-102 -176 -61 0\n-267 -278 270 0\n-236 -224 240 0\n-115 -179 0\n-304 -317 301 0\n-4 196 0\n-40 232 0\n-12 -157 -98 0\n-334 -367 335 0\n-168 360 0\n-285 -296 288 0\n-254 -239 255 0\n-333 -355 331 0\n-346 -335 351 0\n-232 -252 228 0\n-811 66 68 70 71 82 84 86 87 98 100 102 103 0\n-777 234 0\n-88 -123 0\n-53 245 0\n-309 -294 310 0\n-611 -157 -2 0\n-210 0\n-223 -242 218 0\n-195 -215 199 0\n-285 -290 282 0\n-765 11 13 14 27 29 30 0\n-811 263 0\n-314 -270 318 0\n-204 -222 206 0\n-25 217 0\n-27 219 0\n-20 -160 -123 0\n-830 184 178 179 180 181 136 130 131 132 133 0\n-223 -243 219 0\n-175 367 0\n-268 -281 265 0\n753 754 755 0\n-358 -362 354 0\n813 814 815 0\n-75 267 0\n-303 -307 299 0\n-87 -56 -187 0\n-810 199 0\n-371 -344 376 0\n-790 271 0\n-286 -298 282 0\n-131 -20 -89 0\n-60 -160 0\n-358 -364 356 0\n-72 264 0\n-4 -96 -185 0\n-173 365 0\n-2 -111 616 0\n-377 -327 383 0\n-253 -231 255 0\n-308 -281 305 0\n-134 -111 -49 0\n-630 -75 -121 631 0\n-610 -20 -185 611 0\n-354 -332 356 0\n-690 -175 -38 0\n-553 -75 -47 0\n-94 286 0\n-382 -363 379 0\n-547 -148 -56 0\n-67 -20 -153 0\n-372 -352 376 0\n-136 328 0\n-689 -166 -93 0\n-377 -325 381 0\n-118 310 0\n-803 363 0\n-349 -353 345 0\n-76 268 0\n-810 6 7 14 15 22 23 30 31 38 39 0\n-94 -158 0\n-314 -269 317 0\n-755 175 176 169 0\n-532 -75 -166 533 0\n-261 -294 262 0\n-133 -102 -41 0\n-272 -313 265 0\n795 796 797 0\n-575 -148 -120 0\n-241 -198 246 0\n56 63 120 127 184 191 0\n-85 -167 -51 0\n-822 227 0\n-808 124 125 68 69 76 77 84 85 0\n-132 324 0\n-108 300 0\n-140 332 0\n-352 -381 349 0\n-93 -168 -60 0\n-672 -75 -2 0\n-243 -214 246 0\n29 36 93 100 157 164 0\n-70 -48 -185 0\n-298 -267 299 0\n-821 159 160 154 167 168 162 175 176 170 135 136 130 0\n-753 47 41 63 57 0\n-312 -314 306 0\n-789 207 0\n-197 -231 199 0\n-382 -367 383 0\n-604 -93 -2 605 0\n-197 -232 200 0\n-312 -318 310 0\n-567 -75 -175 0\n-222 -239 223 0\n-325 -354 322 0\n-788 326 0\n-69 -38 -169 0\n-133 -161 0\n-736 314 0\n6 41 70 105 134 169 0\n-306 -272 312 0\n-336 -379 331 0\n-448 -75 -148 449 0\n-781 307 0\n-808 317 0\n-251 -214 254 0\n-548 -157 -121 0\n-142 334 0\n-525 -75 -166 0\n-790 77 78 79 85 86 87 93 94 95 0\n-810 5 6 7 13 14 15 21 22 23 29 30 31 0\n-730 304 0\n-333 -353 329 0\n-560 -75 -47 561 0\n-102 -47 -181 0\n-369 -326 374 0\n-296 -316 292 0\n-169 361 0\n-317 -289 313 0\n-821 157 158 159 154 189 190 191 186 133 134 135 130 0\n-22 -111 -179 0\n-160 -188 0\n-830 179 181 187 189 131 133 139 141 155 157 0\n-280 -314 274 0\n-126 318 0\n-315 -279 319 0\n-47 -120 -190 0\n-335 -369 329 0\n-130 -130 0\n-269 -296 272 0\n-379 -341 381 0\n-54 246 0\n747 748 749 0\n-143 335 0\n-352 -377 345 0\n-329 0\n-379 -343 383 0\n-814 76 77 78 79 80 84 85 86 87 88 0\n-2 -166 567 0\n-125 317 0\n-2 -56 630 0\n-164 356 0\n-2 -47 588 0\n-824 163 171 179 187 131 139 0\n-729 240 0\n-215 -241 209 0\n-244 -222 246 0\n-824 168 161 163 176 169 171 184 177 179 144 137 139 0\n-289 -260 292 0\n-773 157 160 173 176 181 184 0\n-334 -363 331 0\n-153 345 0\n-603 -20 -121 604 0\n20 84 148 0\n-73 265 0\n-226 -204 228 0\n-371 -337 369 0\n-240 -253 237 0\n-317 -295 319 0\n-93 -157 0\n222 286 350 0\n-2 -148 497 0\n-830 184 177 179 180 181 144 137 139 140 141 0\n-2 -142 -105 0\n-227 -212 228 0\n-70 262 0\n-782 371 0\n-749 351 0\n4 25 68 89 132 153 0\n810 811 812 0\n-225 -196 228 0\n-2 -143 -113 0\n-770 148 151 164 167 172 175 0\n-380 -351 383 0\n-319 0\n-245 -230 246 0\n-5 -102 -169 0\n21 35 85 99 149 163 0\n-236 -223 239 0\n-288 -314 282 0\n-113 305 0\n223 287 351 0\n-365 0\n-158 -112 -60 0\n-341 -354 338 0\n-2 -111 602 0\n-20 -159 -115 0\n-305 -262 310 0\n-240 -251 235 0\n-146 338 0\n-277 -296 280 0\n-31 223 0\n-824 167 163 175 171 191 187 135 131 143 139 0\n-772 94 96 102 104 118 120 0\n765 766 767 0\n-2 -137 0\n-40 -168 0\n-231 -243 227 0\n-2 -93 532 0\n-345 -325 349 0\n-809 381 0\n-771 224 0\n-833 186 187 188 189 190 130 131 132 133 134 0\n-345 -323 347 0\n-102 -48 -189 0\n-314 -268 316 0\n-749 159 167 175 0\n744 745 746 0\n-63 255 0\n-449 -148 -93 0\n-736 122 66 0\n216 280 344 0\n47 111 175 0\n16 58 80 122 144 186 0\n-771 29 30 32 53 54 56 0\n-21 -149 0\n-778 298 0\n-22 -112 -187 0\n-94 -176 -60 0\n-824 167 168 161 162 163 175 176 169 170 171 0\n-90 282 0\n-267 -273 265 0\n-190 382 0\n-296 -315 291 0\n-746 148 150 164 166 0\n30 44 94 108 158 172 0\n-769 84 85 86 87 0\n-813 208 0\n-727 102 103 0\n-198 -240 200 0\n-368 -377 361 0\n-751 102 104 118 120 0\n-796 94 89 102 97 118 113 126 121 0\n-93 -167 -52 0\n-292 0\n214 278 342 0\n-470 -20 -38 471 0\n-354 -336 360 0\n-785 380 0\n-86 -150 0\n-801 235 0\n-280 -316 276 0\n-251 -215 255 0\n-253 -225 249 0\n-824 168 163 176 171 184 179 136 131 144 139 0\n-142 -170 0\n-212 -218 210 0\n-206 -240 208 0\n-334 -361 329 0\n-295 -312 296 0\n-222 -234 218 0\n-798 38 39 40 33 34 0\n-768 21 22 23 29 30 31 0\n-233 -197 237 0\n-371 -342 374 0\n-497 -75 -157 0\n-385 -75 -11 0\n-2 -80 -185 0\n5 33 69 97 133 161 0\n-3 -131 0\n768 769 770 0\n32 60 96 124 160 188 0\n-294 -304 296 0\n-686 -75 -2 687 0\n-195 -216 200 0\n-2 -38 553 0\n-66 -66 0\n-372 -350 374 0\n-45 237 0\n-116 308 0\n-2 -184 651 0\n-354 -334 358 0\n-2 -93 518 0\n-361 -323 363 0\n215 279 343 0\n-104 296 0\n-346 -333 349 0\n-41 -169 0\n-762 5 13 21 29 0\n-105 297 0\n-150 -171 0\n-297 -261 301 0\n-69 -161 0\n-9 201 0\n-214 -233 209 0\n-4 -93 -161 0\n-2 194 0\n-282 -267 283 0\n-82 274 0\n-772 288 0\n-23 -115 0\n208 272 336 0\n-350 -363 347 0\n-818 152 145 160 153 168 161 176 169 184 177 0\n253 317 381 0\n-69 -40 -185 0\n-823 102 98 99 118 114 115 126 122 123 70 66 67 0\n-140 -32 -122 0\n-303 -305 297 0\n-213 -231 215 0\n-739 66 68 82 84 0\n-747 223 0\n-754 111 105 127 121 0\n-194 -208 200 0\n-133 -103 -49 0\n-298 -272 304 0\n780 781 782 0\n-827 364 0\n-343 -372 340 0\n-249 -199 255 0\n-121 313 0\n-269 -289 265 0\n-825 41 42 43 44 49 50 51 52 57 58 59 60 0\n-820 282 0\n-204 -223 207 0\n-483 -75 -29 484 0\n-59 -123 0\n-78 270 0\n-115 307 0\n-99 291 0\n-265 0\n-826 300 0\n-781 120 113 114 115 0\n-637 -75 -185 638 0\n-760 315 0\n-811 66 69 70 71 82 85 86 87 90 93 94 95 0\n-533 -148 -111 0\n828 829 830 0\n-180 372 0\n-50 242 0\n-808 121 124 125 73 76 77 81 84 85 0\n-30 222 0\n-350 -368 352 0\n-381 -359 383 0\n-98 290 0\n-124 316 0\n816 817 818 0\n-324 -346 322 0\n-271 -305 265 0\n-609 -75 -56 610 0\n225 289 353 0\n-2 -120 658 0\n-688 -93 -20 689 0\n-250 -206 254 0\n-299 -280 304 0\n-738 196 0\n-228 0\n-2 -121 686 0\n14 42 78 106 142 170 0\n-291 -278 294 0\n-811 69 70 71 77 78 79 85 86 87 93 94 95 0\n-300 -285 301 0\n-344 -378 338 0\n-248 -251 243 0\n-214 -239 215 0\n-285 -291 283 0\n-574 -75 -111 0\n-383 0\n8 57 72 121 136 185 0\n224 288 352 0\n-823 102 103 104 97 98 99 0\n-830 181 189 133 141 149 157 0\n-58 -186 0\n-102 294 0\n-691 -184 -111 0\n-833 187 190 131 134 139 142 155 158 163 166 0\n-61 253 0\n-157 -38 -108 0\n-13 -34 0\n-602 -75 -56 603 0\n-299 -277 301 0\n-689 -38 -93 690 0\n-143 -56 -122 0\n-799 102 97 98 118 113 114 126 121 122 0\n-337 -325 341 0\n-367 -373 365 0\n-5 -103 -177 0\n-787 66 68 70 82 84 86 98 100 102 0\n-71 263 0\n245 309 373 0\n-179 371 0\n-215 -242 210 0\n-33 -161 0\n-337 -322 338 0\n-2 -56 637 0\n-205 -231 207 0\n-833 187 188 189 190 131 132 133 134 139 140 141 142 0\n-151 343 0\n-368 -381 365 0\n-222 -235 219 0\n735 736 737 0\n-47 239 0\n-797 345 0\n-134 -47 -113 0\n-764 130 131 132 133 0\n-177 369 0\n-86 -48 -187 0\n-14 206 0\n-112 304 0\n-825 47 41 43 44 63 57 59 60 15 9 11 12 0\n-253 -230 254 0\n-88 280 0\n-264 0\n-828 51 53 59 61 3 5 11 13 27 29 0\n-122 -144 0\n-312 -317 309 0\n-766 76 77 78 84 85 86 0\n804 805 806 0\n-780 243 0\n-800 354 0\n-753 233 0\n-232 -251 227 0\n-241 -194 242 0\n-782 184 179 136 131 144 139 0\n-79 -56 -186 0\n-334 -368 336 0\n-22 -43 0\n-448 -75 -84 0\n-189 381 0\n-48 240 0\n-314 -271 319 0\n-68 -32 -185 0\n-821 160 154 168 162 176 170 184 178 136 130 0\n-833 187 189 190 131 133 134 139 141 142 155 157 158 0\n-86 278 0\n-828 245 0\n-638 -148 -2 0\n-6 198 0\n-808 122 125 66 69 82 85 90 93 0\n-823 291 0\n-14 -78 0\n-2 -29 511 0\n-36 228 0\n-2 -20 462 0\n218 282 346 0\n40 61 104 125 168 189 0\n-2 -57 672 0\n-833 190 134 142 150 158 166 0\n-318 -303 319 0\n-200 0\n-222 -233 217 0\n-152 -187 0\n-171 363 0\n-561 -148 -120 0\n-4 -95 -177 0\n-225 -195 227 0\n750 751 752 0\n-332 -352 336 0\n22 43 86 107 150 171 0\n-166 -48 -125 0\n-150 -112 -59 0\n-212 -223 215 0\n31 52 95 116 159 180 0\n24 59 88 123 152 187 0\n-123 -187 0\n-814 79 80 87 88 95 96 103 104 111 112 0\n-504 -75 -38 0\n-763 66 69 82 85 90 93 0\n-114 306 0\n-651 -75 -185 0\n-166 -111 -53 0\n831 832 833 0\n-182 374 0\n-151 -56 -123 0\n-212 -217 209 0\n-158 -111 -52 0\n-2 -175 609 0\n-359 -371 355 0\n-131 323 0\n-251 -213 253 0\n-766 270 0\n-799 290 0\n-2 -79 -177 0\n-373 -360 376 0\n-194 -206 198 0\n-726 231 0\n-234 -205 237 0\n-75 -152 -58 0\n-96 288 0\n-12 204 0\n-111 -56 -190 0\n-728 359 0\n-13 205 0\n-261 -290 258 0\n-75 -20 -154 0\n-825 47 48 41 42 43 44 0\n-219 0\n-796 281 0\n-20 -96 -187 0\n-767 334 0\n-772 93 95 96 109 111 112 0\n-335 -371 331 0\n-150 -48 -123 0\n786 787 788 0\n-69 261 0\n-307 -280 312 0\n-262 -298 258 0\n-5 197 0\n207 271 335 0\n-815 336 0\n798 799 800 0\n-574 -75 -175 575 0\n-805 120 113 114 116 88 81 82 84 0\n-752 360 0\n209 273 337 0\n-816 209 0\n-336 -380 332 0\n-250 -205 253 0\n-368 -380 364 0\n-142 -48 -122 0\n-32 224 0\n-103 295 0\n-350 -361 345 0\n-352 -382 350 0\n-283 0\n-67 259 0\n-246 0\n-152 344 0\n-93 -38 -172 0\n-47 -111 0\n-367 -371 363 0\n-161 353 0\n-759 251 0\n-59 -187 0\n56 120 184 0\n-754 297 0\n-827 175 176 172 135 136 132 143 144 140 151 152 148 0\n-807 57 59 61 9 11 13 25 27 29 0\n-6 -134 0\n-771 29 30 31 32 0\n-505 -148 -47 0\n251 315 379 0\n-833 189 190 133 134 141 142 149 150 157 158 0\n-811 66 67 68 69 70 71 0\n-824 166 163 182 179 190 187 134 131 142 139 0\n-149 -104 -59 0\n-609 -75 -184 0\n-819 218 0\n-818 148 149 151 152 145 172 173 175 176 169 0\n-111 303 0\n-313 -263 319 0\n-277 -289 273 0\n-141 333 0\n-377 -323 379 0\n-346 -336 352 0\n-2 -38 546 0\n-15 207 0\n-787 66 67 68 69 70 0\n-326 -368 328 0\n-747 29 31 45 47 0\n-289 -262 294 0\n38 102 166 0\n-369 -325 373 0\n-332 -351 335 0\n-134 326 0\n241 305 369 0\n-325 -359 327 0\n205 269 333 0\n-38 230 0\n-829 309 0\n-127 319 0\n-85 -149 0\n-199 -248 200 0\n-33 -69 0\n-2 -78 -169 0\n-259 -277 261 0\n-316 -286 318 0\n-22 214 0\n-326 -362 322 0\n-20 212 0\n-267 -279 271 0\n-44 236 0\n-818 148 150 151 152 145 164 166 167 168 161 0\n-768 215 0\n-2 -102 560 0\n-304 -316 300 0\n-260 -285 261 0\n-95 287 0\n-81 273 0\n-807 57 61 9 13 17 21 25 29 0\n-291 -276 292 0\n-518 -75 -102 0\n-70 -105 0\n-332 -345 329 0\n-744 214 0\n-52 244 0\n-48 -112 0\n-149 341 0\n759 760 761 0\n-783 57 58 59 60 0\n-335 -373 333 0\n-51 243 0\n-187 379 0\n-209 -194 210 0\n-356 0\n-287 -312 288 0\n-504 -75 -102 505 0\n-225 -198 230 0\n-166 -112 -61 0\n-213 -230 214 0\n-5 -104 -185 0\n-13 -77 0\n-58 250 0\n-163 355 0\n-31 -52 0\n-185 377 0\n-832 318 0\n-688 -157 -20 0\n-16 208 0\n-68 -31 -177 0\n-353 -326 358 0\n-157 -104 -60 0\n-370 -334 374 0\n-828 53 61 5 13 21 29 0\n-364 -349 365 0\n-186 378 0\n-338 0\n-236 -221 237 0\n-323 -342 326 0\n-6 -111 -177 0\n-773 352 0\n822 823 824 0\n-75 -150 -42 0\n-123 315 0\n-735 250 0\n-117 309 0\n-207 -248 208 0\n-93 -39 -180 0\n-21 213 0\n-184 376 0\n-252 -223 255 0\n226 290 354 0\n-298 -269 301 0\n-176 368 0\n227 291 355 0\n-588 -75 -56 0\n-808 121 122 123 124 125 0\n-196 -223 199 0\n-181 373 0\n-760 121 122 123 0\n-831 254 0\n-14 -112 -186 0\n-150 -111 -51 0\n-735 57 58 0\n-157 -102 -44 0\n-761 187 131 139 0\n-797 157 158 160 153 181 182 184 177 0\n-67 -131 0\n-239 -241 233 0\n-342 -362 338 0\n3 17 67 81 131 145 0\n-31 -116 0\n-296 -314 290 0\n-205 -232 208 0\n-343 -376 344 0\n-310 0\n801 802 803 0\n-214 -234 210 0\n-336 -377 329 0\n-804 51 52 59 60 3 4 11 12 0\n-239 -242 234 0\n762 763 764 0\n-786 6 14 22 30 38 0\n-787 66 70 82 86 90 94 98 102 0\n-4 -157 -97 0\n-42 234 0\n-373 -358 374 0\n-547 -20 -56 548 0\n-807 253 0\n244 308 372 0\n-167 359 0\n-56 248 0\n-786 198 0\n-371 -341 373 0\n-212 -222 214 0\n-97 289 0\n-294 -300 292 0\n-2 -157 525 0\n-279 -305 273 0\n-759 57 59 9 11 0\n-780 51 59 3 11 0\n-231 -244 228 0\n-35 227 0\n-87 279 0\n-159 351 0\n-658 -75 -121 0\n-342 -368 344 0\n-289 -259 291 0\n-364 -351 367 0\n-802 299 0\n-97 -161 0\n-103 -56 -189 0\n-323 -343 327 0\n825 826 827 0\n-2 -75 448 0\n-103 -167 0\n-341 -360 344 0\n-2 -2 385 0\n39 53 103 117 167 181 0\n771 772 773 0\n-93 285 0\n-826 105 108 113 116 121 124 73 76 81 84 0\n-235 -212 236 0\n-765 11 14 27 30 35 38 0\n197 261 325 0\n-230 -236 228 0\n-7 -120 -185 0\n-305 -261 309 0\n-605 -166 -75 0\n-818 148 149 150 152 145 180 181 182 184 177 0\n-263 -307 259 0\n-201 0\n-167 -56 -125 0\n-78 -106 0\n-511 -75 -38 0\n236 300 364 0\n-260 -288 264 0\n-49 -177 0\n-323 -344 328 0\n-195 -213 197 0\n-2 -29 504 0\n-469 -75 -157 470 0\n-224 -253 221 0\n-20 -94 -171 0\n-258 -272 264 0\n-817 273 0\n-122 314 0\n-278 -297 273 0\n-240 -250 234 0\n-379 -337 377 0\n-255 0\n-239 -245 237 0\n-7 199 0\n738 739 740 0\n-178 370 0\n-307 -277 309 0\n-263 -312 264 0\n-786 3 6 11 14 27 30 35 38 0\n-316 -287 319 0\n-213 -226 210 0\n-188 380 0\n-818 148 151 152 145 164 167 168 161 172 175 176 169 0\n-155 347 0\n-344 -382 342 0\n-287 -307 283 0\n-316 -285 317 0\n-777 48 41 42 56 49 50 0\n-112 -176 0\n-575 -20 -120 576 0\n-342 -367 343 0\n-560 -75 -111 0\n13 34 77 98 141 162 0\n-191 383 0\n-347 0\n-100 292 0\n-325 -355 323 0\n-270 -297 265 0\n-791 335 0\n-123 -152 0\n-2 -77 -161 0\n-106 298 0\n-242 -205 245 0\n783 784 785 0\n-31 -120 -188 0\n-3 195 0\n-737 186 130 0\n-325 -360 328 0\n-75 -149 -34 0\n-788 130 131 132 134 162 163 164 166 0\n-41 233 0\n-833 188 189 190 132 133 134 140 141 142 148 149 150 0\n-374 0\n-471 -157 -175 0\n-784 316 0\n-745 278 0\n232 296 360 0\n-20 -93 -163 0\n726 727 728 0\n-616 -75 -120 0\n-158 350 0\n-532 -75 -102 0\n-342 -364 340 0\n198 262 326 0\n-780 49 51 57 59 9 11 0\n-89 281 0\n-69 -97 0\n-376 -382 374 0\n-224 -251 219 0\n-237 0\n-274 0\n-8 200 0\n-803 176 171 184 179 136 131 144 139 0\n75 0\n-68 260 0\n-5 -161 0\n12 26 76 90 140 154 0\n-791 139 140 143 163 164 167 171 172 175 0\n-469 -75 -29 0\n-20 -148 0\n-2 -102 574 0\n-79 271 0\n-355 -343 359 0\n-690 -111 -38 691 0\n-59 -152 0\n-827 172 180 188 132 140 148 0\n-779 362 0\n-808 121 122 124 125 81 82 84 85 0\n-748 287 0\n-303 -309 301 0\n-262 -304 264 0\n-352 -379 347 0\n-762 197 0\n-791 139 140 141 143 171 172 173 175 0\n-781 113 114 115 121 122 123 0\n-160 352 0\n-740 324 0\n-109 301 0\n-823 102 103 97 98 99 126 127 121 122 123 0\n-157 349 0\n48 62 112 126 176 190 0\n-75 -139 0\n-462 -75 -29 0\n-351 -371 347 0\n-26 218 0\n-827 175 176 171 172 135 136 131 132 143 144 139 140 0\n-59 251 0\n-159 -56 -124 0\n-806 372 0\n231 295 359 0\n-86 -47 -179 0\n-14 -176 -122 0\n-17 209 0\n-361 -325 365 0\n-131 -24 -121 0\n-33 225 0\n-162 354 0\n-341 -359 343 0\n-737 378 0\n217 281 345 0\n-20 -157 -99 0\n-328 0\n-631 -20 -2 632 0\n-207 -241 201 0\n-285 -295 287 0\n-77 269 0\n-133 325 0\n-62 254 0\n-22 -150 0\n-798 39 40 33 34 47 48 41 42 0\n-381 -355 379 0\n-259 -278 262 0\n-362 -333 365 0\n-349 -355 347 0\n-323 -341 325 0\n-281 -259 283 0\n-172 364 0\n-149 -38 -107 0\n-316 -281 313 0\n-546 -75 -111 547 0\n-833 187 188 190 131 132 134 139 140 142 163 164 166 0\n-49 -113 0\n-144 336 0\n-326 -364 324 0\n-120 312 0\n-350 -367 351 0\n-85 277 0\n-115 -151 0\n-93 -166 -44 0\n-359 -372 356 0\n240 304 368 0\n7 49 71 113 135 177 0\n-576 -157 -185 0\n-87 -179 0\n-778 106 114 122 66 0\n-159 -120 -60 0\n807 808 809 0\n-71 -56 -185 0\n-809 189 133 141 149 157 0\n-43 -150 0\n-261 -296 264 0\n-39 231 0\n-241 -197 245 0\n819 820 821 0\n-750 232 0\n-69 -166 -41 0\n196 260 324 0\n-49 241 0\n-827 175 176 170 172 135 136 130 132 151 152 146 148 0\n-43 235 0\n-60 252 0\n-332 -349 333 0\n213 277 341 0\n-134 -169 0\n-761 379 0\n-331 -337 329 0\n-755 361 0\n-135 327 0\n-824 355 0\n-2 -20 469 0\n-286 -299 283 0\n252 316 380 0\n-788 130 131 132 133 134 0\n-230 -240 232 0\n-484 -148 -166 0\n-196 -224 200 0\n-825 48 41 42 43 44 56 49 50 51 52 0\n-327 -371 323 0\n-248 -254 246 0\n-814 76 78 79 80 84 86 87 88 100 102 103 104 0\n-30 -158 0\n789 790 791 0\n-252 -222 254 0\n-166 358 0\n-360 -380 356 0\n-23 215 0\n-830 373 0\n-795 217 0\n-812 327 0\n-802 112 105 106 107 120 113 114 115 0\n-811 66 67 68 70 71 98 99 100 102 103 0\n-787 262 0\n-368 -379 363 0\n-279 -306 274 0\n-344 -380 340 0\n-814 80 88 96 104 112 120 0\n-76 -140 0\n-340 -346 338 0\n-687 -20 -75 688 0\n-821 157 159 160 154 173 175 176 170 133 135 136 130 0\n-783 57 59 60 9 11 12 0\n-2 -148 483 0\n-821 157 158 159 160 154 133 134 135 136 130 0\n-301 0\n-382 -364 380 0\n-818 148 149 150 151 145 188 189 190 191 185 0\n729 730 731 0\n-747 29 30 31 0\n-773 160 168 176 184 0\n-223 -241 217 0\n"
 "990 -130 0 179 0\n991 -173 0 233 86 0\n992 -833 186 187 188 189 190 131 132 133 134 0 990 253 0\n993 -212 -218 0 56 297 0\n994 -334 -361 0 186 299 0\n995 -66 0 317 0\n996 2 0 995 990 27 0\n997 -137 0 996 246 0\n998 -184 651 0 996 321 0\n999 -93 518 0 996 323 0\n1000 194 0 996 337 0\n1001 -823 102 98 99 118 114 115 126 122 123 70 67 0 995 347 0\n1002 -739 68 82 84 0 995 351 0\n1003 -208 200 0 1000 354 0\n1004 -73 0 371 205 0\n1005 -811 69 70 71 82 85 86 87 90 93 94 95 0 995 376 0\n1006 -808 121 124 125 76 77 81 84 85 0 1004 381 0\n1007 -271 -305 0 371 389 0\n1008 -120 658 0 996 392 0\n1009 -121 686 0 996 398 0\n1010 -367 -373 0 233 426 0\n1011 -787 68 70 82 84 86 98 100 102 0 995 428 0\n1012 -215 -242 0 56 432 0\n1013 -56 637 0 996 435 0\n1014 -368 -381 0 233 439 0\n1015 -764 131 132 133 0 990 445 0\n1016 -72 0 453 84 0\n1017 -241 242 0 1000 463 0\n1018 -314 -271 0 225 471 0\n1019 -821 160 154 168 162 176 170 184 178 136 0 990 473 0\n1020 -638 -148 0 996 477 0\n1021 -808 122 125 69 82 85 90 93 0 995 479 0\n1022 -29 511 0 996 482 0\n1023 -36 0 397 483 0\n1024 -20 462 0 996 484 0\n1025 -57 672 0 996 487 0\n1026 -318 -303 0 225 489 0\n1027 -208 0 490 1003 0\n1028 -813 0 1027 278 0\n1029 -763 69 82 85 90 93 0 995 508 0\n1030 -175 609 0 996 517 0\n1031 -79 -177 0 996 523 0\n1032 -206 198 0 1000 525 0\n1033 -27 0 537 65 0\n1034 -54 0 567 182 0\n1035 -807 57 59 61 9 11 13 25 29 0 1033 578 0\n1036 -811 67 68 69 70 71 0 995 584 0\n1037 -818 148 149 151 152 145 172 175 176 169 0 991 589 0\n1038 -313 -263 0 225 591 0\n1039 -38 546 0 996 596 0\n1040 -787 67 68 69 70 0 995 598 0\n1041 -127 0 225 611 0\n1042 -199 -248 0 490 613 0\n1043 -78 -169 0 996 615 0\n1044 -102 560 0 996 625 0\n1045 -291 -276 0 285 631 0\n1046 -332 -345 0 186 634 0\n1047 -209 0 1000 56 644 0\n1048 -816 0 1047 556 0\n1049 -164 0 645 192 0\n1050 -16 0 1027 659 0\n1051 -364 -349 0 233 665 0\n1052 -146 0 667 240 0\n1053 -207 -248 0 1027 677 0\n1054 -342 -362 0 667 700 0\n1055 -205 -232 0 1027 704 0\n1056 -118 0 706 105 0\n1057 -214 -234 0 56 708 0\n1058 -336 -377 0 186 709 0\n1059 -787 70 82 86 90 94 98 102 0 995 714 0\n1060 -294 -300 0 285 727 0\n1061 -157 525 0 996 728 0\n1062 -231 -244 0 397 732 0\n1063 -75 448 0 996 745 0\n1064 385 0 996 748 0\n1065 -826 105 108 113 116 121 124 76 81 84 0 1004 752 0\n1066 -765 11 14 30 35 38 0 1033 754 0\n1067 -230 -236 0 397 756 0\n1068 -9 0 762 334 0\n1069 -260 -288 0 453 767 0\n1070 -29 504 0 996 771 0\n1071 -258 -272 0 453 775 0\n1072 -63 0 781 259 0\n1073 -263 -312 0 453 787 0\n1074 -786 3 6 11 14 30 35 38 0 1033 788 0\n1075 -316 -287 0 225 789 0\n1076 -213 -226 0 56 790 0\n1077 -818 148 151 152 145 167 168 161 172 175 176 169 0 1049 792 0\n1078 -287 -307 0 565 795 0\n1079 -191 0 408 803 0\n1080 -155 0 804 793 0\n1081 -100 0 285 805 0\n1082 -270 -297 0 371 807 0\n1083 -77 -161 0 996 810 0\n1084 -737 186 0 990 816 0\n1085 -788 131 132 134 162 163 166 0 990 1049 819 0\n1086 -182 0 822 513 0\n1087 -780 49 51 57 59 11 0 1068 834 0\n1088 -376 -382 0 822 837 0\n1089 -224 -251 0 537 838 0\n1090 -45 0 839 319 0\n1091 -82 0 840 339 0\n1092 -8 0 490 841 0\n1093 -145 0 843 996 33 0\n1094 267 0 843 74 0\n1095 -672 0 843 996 129 0\n1096 -11 0 843 1064 307 0\n1097 448 0 843 1063 0\n1098 -273 0 1094 371 272 0\n1099 -282 0 1094 565 338 0\n1100 -57 0 1095 1025 0\n1101 -84 0 1097 843 468 0\n1102 337 0 1098 1047 555 0\n1103 -81 0 1098 629 0\n1104 -817 0 1098 776 0\n1105 -90 0 1099 271 0\n1106 -820 0 1099 364 0\n1107 -322 0 1102 667 434 0\n1108 818 0 1104 1048 387 0\n1109 12 26 76 140 154 0 1105 846 0\n1110 -791 139 140 143 163 167 171 172 175 0 1049 847 0\n1111 -469 -29 0 843 848 0\n1112 -102 574 0 996 850 0\n1113 -808 121 122 124 125 85 0 1103 1091 1101 857 0\n1114 -262 -304 0 453 860 0\n1115 -352 -379 0 804 861 0\n1116 -791 139 140 141 143 171 172 175 0 991 863 0\n1117 -823 102 103 97 98 99 126 121 122 123 0 1041 868 0\n1118 -139 0 843 871 0\n1119 -462 -29 0 843 872 0\n1120 -351 -371 0 804 873 0\n1121 -827 175 176 171 172 135 136 131 132 143 144 140 0 1118 875 0\n1122 -17 0 1047 882 0\n1123 -361 -325 0 233 883 0\n1124 -136 0 891 102 0\n1125 -631 -20 632 0 996 892 0\n1126 -207 -241 0 762 893 0\n1127 -362 -333 0 233 902 0\n1128 -349 -355 0 804 903 0\n1129 -281 -259 0 565 905 0\n1130 -546 -111 547 0 843 909 0\n1131 -833 187 188 190 131 132 134 140 142 163 166 0 1118 1049 910 0\n1132 -359 -372 0 645 919 0\n1133 -778 106 114 122 0 995 924 0\n1134 -261 -296 0 453 930 0\n1135 819 821 0 1106 933 0\n1136 -827 175 176 170 172 135 132 151 152 148 0 1124 990 1052 938 0\n1137 -331 0 1102 186 945 0\n1138 -20 469 0 996 949 0\n1139 -286 -299 0 565 950 0\n1140 -788 131 132 133 134 0 990 952 0\n1141 -196 -224 0 490 955 0\n1142 -248 -254 0 567 958 0\n1143 -814 76 78 79 80 86 87 88 102 103 104 0 1101 1081 959 0\n1144 -360 -380 0 645 964 0\n1145 -811 67 68 70 71 98 99 102 103 0 995 1081 970 0\n1146 -279 -306 0 840 973 0\n1147 -340 -346 0 667 977 0\n1148 -687 -20 688 0 843 978 0\n1149 -821 157 159 160 154 175 176 170 133 135 0 991 1124 990 979 0\n1150 -783 59 60 12 0 1100 1068 1096 980 0\n1151 -148 483 0 996 981 0\n1152 -821 157 158 159 160 154 133 134 135 0 1124 990 982 0\n1153 -109 0 983 867 0\n1154 148 149 150 151 188 189 190 185 0 1108 1093 1079 985 0\n1155 -318 -382 0 408 706 843 996 1088 680 139 69 142 1026 914 590 575 263 686 193 0\n1156 296 24 125 -149 88 187 189 152 227 61 360 0 44 326 826 486 462 9 876 504 0\n1157 -336 -364 -373 -111 -382 0 567 1047 397 996 1099 1023 1081 822 843 1049 565 1137 225 1124 1100 1092 1016 983 371 490 1093 1103 1122 285 1101 407 1112 717 963 602 507 1070 1051 869 131 751 406 370 59 590 859 26 1088 680 87 829 575 1039 1130 99 204 827 620 993 485 1147 832 794 568 327 984 215 733 609 1067 753 515 722 1142 451 719 417 226 53 5 524 676 12 152 288 557 595 1058 251 469 345 643 98 682 1046 101 656 926 39 209 23 1076 889 720 409 562 395 421 679 70 1129 1062 361 262 452 916 108 566 931 116 315 228 749 815 763 701 884 1156 45 167 180 1134 1069 386 895 545 844 123 0\n1158 381 114 -272 113 141 150 157 43 801 253 -830 -111 0 996 822 843 371 1016 1092 1100 1124 983 233 1080 1118 1098 116 361 409 656 407 1112 966 717 963 602 5 87 829 469 104 345 896 39 412 449 356 638 907 811 16 181 904 106 493 643 519 707 173 38 171 969 499 330 475 778 0\n1159 -827 -830 312 -111 -833 0 397 1047 822 843 1101 1099 1107 1081 1023 565 1027 371 1100 1092 1016 408 1124 1049 1093 1108 996 1056 8 1088 680 87 829 575 407 1112 966 717 963 602 1039 1130 99 204 620 993 485 388 124 1147 609 1067 753 939 291 515 967 215 507 1070 722 1142 451 524 44 1053 531 1155 175 139 69 358 1051 739 832 913 869 327 48 18 794 605 131 593 184 549 568 569 751 1007 406 231 685 1157 342 912 116 151 361 509 409 656 88 947 1158 384 1014 721 852 684 438 577 1136 623 29 126 296 741 1046 488 443 110 117 283 0\n1160 345 152 150 122 305 140 167 114 121 -826 148 166 168 -56 102 126 0 1047 983 1023 1081 843 397 1016 1092 1100 1124 408 371 1049 1093 1108 1101 1103 1056 231 722 1042 409 656 88 3 1038 204 620 215 122 602 507 1070 372 402 751 131 869 1128 948 672 890 418 993 874 515 535 889 107 70 90 1129 908 572 108 320 566 761 386 623 1109 1065 369 514 42 633 1001 0\n1161 -151 131 780 -271 114 121 -56 184 0 1016 1092 1100 1118 1124 1018 777 1007 231 409 656 1058 912 13 514 917 464 864 357 0\n1162 342 140 -271 167 114 -826 166 168 47 -382 0 1099 1107 983 1023 1081 1034 408 1086 996 1101 397 567 1047 804 1049 1093 1108 843 1105 1091 667 490 1056 1018 777 1007 231 372 1060 1088 680 139 69 7 87 829 575 407 1112 602 1039 1130 99 204 620 215 507 1070 402 751 131 869 1128 685 400 718 157 993 485 388 124 609 722 1042 1155 175 18 794 286 568 130 335 1057 459 820 716 1160 254 519 1161 623 25 148 333 433 741 845 266 612 638 818 1015 1029 235 712 460 329 862 15 141 138 424 41 953 931 551 470 899 0\n1163 -214 362 371 122 113 -790 333 114 86 144 80 93 253 -56 309 120 0 567 1099 983 1050 856 217 130 1057 459 6 51 24 357 786 1078 22 80 683 373 916 628 1133 97 608 895 34 764 558 160 653 465 264 0\n1164 -781 51 222 213 22 170 113 -381 114 86 135 172 108 44 148 29 168 312 207 199 -111 175 0 996 983 843 408 1049 667 822 990 1124 781 1101 1091 1103 1096 382 679 1014 684 384 721 204 620 993 588 1135 535 590 859 87 829 154 373 75 546 786 1078 34 341 917 237 1139 452 916 942 858 277 223 257 97 211 235 311 183 276 318 886 303 624 352 516 878 134 702 58 293 365 688 82 553 815 876 530 40 458 710 0\n1165 -59 -150 176 235 62 190 126 0 876 501 239 870 470 0\n1166 333 -381 -826 -830 312 47 -382 0 397 983 1023 1081 1101 996 843 1034 1056 1086 1016 1092 1027 408 1049 1096 1100 1124 1118 997 822 1014 684 384 721 139 69 7 407 1112 966 717 963 602 1039 1130 1088 680 87 829 575 99 204 718 507 1070 372 402 751 131 157 409 656 1058 342 151 509 1060 620 215 869 1128 685 400 825 475 912 88 947 1051 906 308 418 609 1067 753 291 622 722 1142 451 5 524 44 897 1053 137 1042 531 590 859 1155 175 593 641 941 808 549 126 961 1007 1018 231 777 1162 305 1054 217 431 20 1163 618 635 650 725 258 275 331 693 1164 357 1165 731 1087 310 768 842 213 707 379 740 318 1139 211 0\n1167 -780 353 176 167 745 294 148 166 62 190 -111 126 0 983 397 843 1101 1099 1107 1049 1096 1100 567 204 620 993 485 388 124 407 1112 602 609 1067 753 215 226 53 5 590 859 676 459 130 248 635 931 258 749 275 693 1165 731 1087 310 815 937 91 355 496 119 1140 391 723 601 544 971 0\n1168 -49 -781 167 114 -20 120 175 0 1047 154 1078 858 620 515 911 937 373 989 237 352 257 183 0\n1169 -113 140 171 167 -349 789 175 0 996 1118 1128 654 1051 906 231 222 1007 1110 79 961 0\n1170 -150 780 167 114 -263 135 71 -349 -20 29 789 199 47 175 0 1034 1056 1086 996 843 1047 1099 1107 822 1090 1101 1091 620 993 485 388 866 515 783 7 87 829 18 331 305 217 357 154 761 1078 1129 858 889 1046 126 1168 1169 373 921 237 257 183 352 600 688 660 396 1002 784 0\n1171 -781 113 85 70 94 41 167 114 -811 86 135 71 93 -20 -38 7 -111 175 0 996 843 1105 1091 822 983 87 829 154 1168 373 1078 921 34 628 446 670 1005 166 147 545 605 150 332 330 0\n1172 -371 150 780 161 167 114 121 148 166 168 -56 376 0 1016 1092 1100 1124 408 1137 1049 1093 1108 409 656 88 722 1053 680 78 542 568 549 623 438 1161 743 519 0\n1173 -381 -826 -830 312 47 -382 0 397 1023 1081 1101 996 822 843 1034 1056 1086 1016 1092 1100 1124 1027 408 186 1049 567 1047 1099 1094 983 1098 139 69 7 407 1112 966 717 963 602 1039 1130 1088 680 87 829 575 99 204 718 507 1070 372 402 751 131 157 409 656 1058 342 151 509 1071 722 1042 77 88 968 220 1060 620 215 869 1128 685 400 825 475 3 947 927 524 44 1142 897 1053 137 783 531 590 859 1155 175 384 1014 721 684 1166 163 1127 572 1167 1170 275 258 635 130 335 1057 820 24 80 133 547 683 97 421 216 895 916 1172 217 6 357 1078 1171 628 231 349 1007 729 758 1082 851 734 545 368 401 0\n1174 -261 97 103 258 -823 99 102 0 534 1134 385 326 411 0\n1175 122 98 125 782 -167 49 97 103 -808 -823 99 121 93 -111 126 0 983 1016 1092 1124 1027 843 1105 1091 1096 1100 407 1112 409 656 1058 342 1071 1174 545 590 859 1117 1021 367 121 916 1087 786 357 154 0\n1176 -122 30 767 125 -176 -296 -808 121 29 318 0 285 840 1101 1103 1033 1096 167 386 777 881 62 174 256 521 241 108 245 916 1006 60 652 0\n1177 -830 312 47 -833 0 1034 1086 996 822 843 567 1101 397 1049 1081 1023 1124 1100 1092 1016 408 1027 983 225 490 285 1056 8 1088 680 139 69 7 87 829 575 722 1142 897 1042 531 590 859 676 407 1112 1155 175 966 524 717 554 963 602 5 1039 609 507 1130 226 451 1067 1070 99 53 719 1 204 620 718 215 122 1159 744 372 402 751 131 157 869 890 409 1128 656 948 88 1058 672 3 342 1038 1071 1173 251 104 345 10 926 39 209 169 289 449 562 726 1174 755 141 138 932 934 826 953 879 931 937 497 167 470 920 518 749 282 386 824 951 870 466 217 763 662 813 962 540 382 1176 687 1175 367 42 1150 0\n1178 -29 -166 0 1101 843 1111 1138 204 1151 954 366 0\n1179 -296 -808 122 125 121 291 0 285 167 274 386 674 687 0\n1180 -123 104 112 -185 120 0 996 1028 565 656 1058 550 73 308 52 674 975 11 529 0\n1181 -124 180 52 31 116 -56 0 386 877 1075 503 628 0\n1182 -808 122 124 125 121 291 120 0 1016 1092 1100 1124 983 409 155 1179 687 39 326 449 1180 0\n1183 -123 771 -185 -20 291 181 157 120 184 0 565 991 674 66 11 274 340 326 750 1180 200 798 0\n1184 -352 -112 760 -824 -377 163 148 373 -382 0 804 1118 1096 1068 1100 1093 1108 185 564 1115 254 343 643 944 519 493 639 194 730 13 431 854 501 724 25 638 0\n1185 -112 104 760 224 103 -166 -111 -382 0 822 1047 397 565 1099 1107 1023 1049 1016 1092 1100 1124 408 996 843 1081 1101 1091 995 1056 1118 252 1088 680 87 829 575 722 1042 77 759 159 1061 1178 131 140 236 420 249 113 377 204 203 409 656 88 968 220 620 993 485 388 124 751 406 480 215 122 672 927 515 64 827 370 59 385 963 717 407 1112 449 1114 216 1184 671 410 750 1069 844 1145 100 566 698 1129 901 835 475 219 50 85 76 923 244 194 774 0\n1186 -171 30 -20 108 44 172 0 804 493 774 343 276 830 0\n1187 -350 131 188 334 -368 133 189 132 141 190 -833 0 891 804 1118 599 605 158 31 343 126 972 437 643 0\n1188 131 188 334 -176 32 124 30 133 189 141 -20 108 44 172 157 190 -833 0 1099 1107 891 1080 1118 684 599 605 158 620 993 485 388 124 8 1187 830 564 276 474 865 269 539 312 0\n1189 -176 32 124 30 189 325 141 -377 -20 108 44 364 157 190 -833 0 891 804 896 1058 906 684 281 466 559 599 158 791 605 1188 519 254 669 904 563 18 638 830 583 0\n1190 122 124 30 189 809 325 125 97 103 -166 -111 -833 0 822 983 645 1047 565 1137 1099 1107 1101 1023 1081 1049 1016 1092 1100 1124 408 996 843 839 397 896 8 1088 680 87 829 575 722 1042 77 759 159 1061 1178 131 140 236 420 249 113 377 204 203 409 656 88 968 220 620 993 485 388 124 751 406 215 685 47 593 480 122 672 927 515 64 827 963 83 402 766 668 370 125 59 385 918 717 689 1142 897 531 407 1112 1155 175 1182 926 719 208 773 470 252 561 1183 690 1189 870 449 1184 1185 1114 410 326 651 216 1069 1134 844 936 545 1145 221 100 566 885 1129 309 835 336 219 0\n1191 -167 97 103 -245 -111 -833 0 1099 983 645 839 397 565 1137 1101 1023 1081 1049 996 843 1016 1092 1100 1124 1028 408 567 840 1094 1118 407 1112 226 609 602 759 159 1061 1178 131 140 236 8 1088 680 87 829 575 420 249 113 377 204 203 409 656 1058 550 73 751 406 620 215 685 47 593 88 308 782 963 83 402 766 229 242 125 590 859 26 320 59 918 906 722 1053 137 1155 139 69 284 721 763 384 1132 607 251 469 379 720 197 382 1181 1186 1190 777 423 62 174 1018 703 368 36 452 79 621 851 326 475 961 734 1143 1116 976 0\n1192 -231 227 29 53 -828 -248 0 781 1033 1096 1053 1042 89 138 248 436 417 548 642 404 533 876 664 454 679 815 770 0\n1193 103 -828 -111 -833 0 822 1099 983 645 565 1137 1016 1092 1100 1124 1023 1081 1049 1101 397 996 843 408 285 567 839 8 1088 680 87 829 575 722 407 1112 476 226 609 602 511 1178 159 1061 131 249 113 377 204 620 215 1192 931 526 1042 759 140 236 420 203 409 656 88 3 1038 77 968 220 751 406 685 47 593 927 782 963 83 402 766 229 242 668 370 125 59 385 590 859 26 320 918 717 689 1142 897 531 676 1155 175 279 828 749 532 284 1191 384 1132 607 726 469 379 720 169 199 738 1181 197 345 844 566 382 208 773 1145 470 561 216 1189 1114 870 449 0\n1194 -97 70 -811 71 291 0 285 726 836 199 738 844 566 1036 0\n1195 -13 188 142 134 41 33 40 133 48 -828 47 -833 0 983 565 1137 1099 1107 1023 1081 1049 1101 397 567 1034 1056 408 1086 996 843 839 645 667 8 1088 680 139 69 7 87 829 575 1193 742 722 407 1112 476 226 609 602 511 1178 159 1061 131 249 113 377 204 620 215 1192 931 993 485 388 124 751 406 685 47 593 963 83 358 402 372 744 59 522 918 531 419 533 302 527 551 716 460 536 94 235 929 126 638 821 0\n1196 -69 176 -807 133 48 -828 47 -833 0 1016 1092 1124 1047 397 565 1137 1023 1081 1049 1101 1099 1107 225 996 567 1034 1056 408 1086 843 983 1072 1122 1096 1068 1100 8 139 69 7 407 1112 476 226 609 602 1088 680 87 829 575 531 722 1142 897 1155 175 870 649 1193 562 209 190 742 159 1061 1178 131 249 113 377 204 620 993 485 388 124 751 406 215 685 47 593 515 64 759 140 236 420 203 409 346 545 614 935 332 1134 135 576 326 71 486 112 946 44 943 994 1144 158 791 1195 630 1035 266 501 583 821 830 126 31 0\n1197 -352 -112 171 123 167 -824 121 163 148 373 -56 -382 0 1016 1092 1100 1124 408 804 1118 1079 409 656 88 947 139 69 185 1115 1184 254 643 690 519 423 243 0\n1198 30 -807 325 -253 -828 47 -833 0 1047 1137 1099 1107 225 983 645 839 1016 1092 1100 1124 1101 1023 1081 1049 565 822 567 1034 408 996 843 397 1056 1086 896 8 1088 680 139 69 7 87 829 407 1112 476 226 609 602 159 1061 963 717 689 1178 131 751 406 249 113 377 204 759 140 236 575 420 203 409 83 402 766 668 773 252 1183 561 208 470 1193 562 209 796 386 746 742 722 1042 77 656 88 968 220 620 993 485 388 124 215 685 47 593 480 122 672 927 515 967 64 827 125 918 906 1142 897 531 1155 175 1186 1189 870 449 1114 216 1194 1196 1197 671 865 410 750 1069 844 936 1036 221 100 566 885 1129 538 835 117 219 336 85 309 651 427 244 697 110 0\n1199 -222 48 217 218 -825 44 47 0 537 301 440 491 716 939 820 536 0\n1200 325 -253 -828 47 -833 0 1099 1107 1137 225 1016 1092 1100 565 822 839 1047 996 1101 983 1023 1081 1049 567 1034 1056 408 1086 645 843 667 397 1118 1124 8 139 69 7 407 1112 476 226 609 602 963 83 906 159 1061 1178 131 918 751 402 125 249 113 377 204 358 372 744 620 993 515 208 470 1199 382 1186 1088 680 87 829 717 689 406 759 140 236 575 420 203 409 766 668 773 252 1183 561 1193 562 209 796 386 155 746 742 722 511 215 1192 931 656 1058 912 685 47 593 485 388 480 122 672 827 59 522 1142 897 531 1155 175 896 1189 1198 870 926 1197 928 410 638 818 1069 235 724 904 936 460 431 519 221 551 295 885 247 302 0\n1201 -253 -828 47 -833 0 822 983 645 1047 397 565 1101 1023 1081 1049 567 1016 1092 1100 1124 1034 1056 408 1086 996 843 839 1102 891 1118 997 8 1088 680 139 69 7 87 829 575 722 1042 77 407 1112 476 226 609 602 759 159 1061 1178 131 140 236 420 249 113 377 204 203 409 656 88 968 220 1058 912 751 406 620 215 685 1128 480 122 672 927 515 993 827 963 83 402 766 668 358 372 744 125 918 906 717 208 773 470 1199 382 1186 1200 104 250 425 603 817 1123 127 1014 889 724 446 44 168 410 684 920 1129 431 198 1069 1114 566 333 844 216 1036 0\n1202 -325 68 70 171 176 -811 144 349 -824 71 217 163 373 184 0 1102 891 1118 997 250 425 603 817 1123 889 724 446 44 168 1129 431 198 566 333 1036 0\n1203 260 70 171 176 -809 189 39 -811 144 141 324 349 -824 71 217 163 799 373 157 38 184 0 397 843 667 1118 1124 844 936 221 885 1202 896 928 638 818 235 724 904 460 431 519 551 295 302 247 0\n1204 48 176 352 -809 189 39 31 38 47 -382 0 822 983 645 1047 397 565 1137 1099 1107 1023 1081 1049 1016 1092 1100 1124 1034 1056 408 1086 996 843 1101 1091 671 1088 680 139 69 7 87 829 575 722 1042 77 407 1112 602 759 159 1061 1178 131 140 236 420 249 113 377 204 203 409 656 88 968 220 1058 912 620 993 485 388 866 751 406 215 685 47 593 1128 480 122 672 927 515 827 963 83 358 402 372 744 125 59 522 918 906 717 1142 897 531 1155 175 1199 870 382 449 1186 1114 216 1203 1069 340 410 750 1141 580 396 472 784 1002 0\n1205 30 70 176 352 -809 189 39 -811 71 -185 31 -20 44 29 172 373 157 38 184 0 983 1047 397 1023 1081 1049 565 1137 1099 1107 1101 1091 671 656 1058 912 620 993 485 388 866 131 751 406 215 685 47 593 1128 480 122 672 515 827 402 125 59 522 1186 1203 1069 340 410 750 1141 580 396 472 784 1002 0\n1206 -828 47 -833 0 1034 1056 1086 567 839 645 822 1049 1081 1023 996 843 983 565 1101 397 1047 1124 1092 1016 408 225 1027 537 1096 1068 1100 1072 8 1088 680 139 69 7 87 829 575 722 1053 597 1042 77 1142 236 420 407 1112 476 226 782 609 602 511 759 159 963 1061 83 717 358 906 1178 131 249 751 918 140 113 402 406 377 372 766 204 744 229 620 203 242 215 515 409 685 656 927 1128 88 968 220 1192 931 1193 562 742 209 155 1201 719 345 926 127 1014 684 1204 132 470 298 1205 382 440 491 962 63 939 239 820 940 530 876 450 0\n1207 47 -833 0 1086 1056 1034 983 996 822 408 1102 1124 1100 1092 1016 1101 843 397 1049 1081 1023 565 8 1088 680 139 69 7 87 590 407 829 859 1112 575 610 191 722 1042 1142 1206 378 966 1177 717 456 1073 963 3 602 88 1039 609 507 656 780 1130 451 1070 409 99 345 92 204 900 1125 620 17 215 131 685 751 406 0\n1208 -222 -825 44 -212 -47 0 996 843 781 1047 567 537 1100 515 993 442 46 193 686 144 197 301 440 491 725 962 57 68 989 636 716 939 820 156 940 380 642 937 956 876 363 470 653 779 0\n1209 -241 31 6 30 29 -833 0 839 1016 1092 1100 1124 408 996 843 1072 1041 1079 567 1047 8 1088 680 1207 193 686 120 914 1073 61 1008 736 409 656 88 968 220 757 96 316 442 782 119 196 1017 1126 932 1032 965 405 812 597 548 448 618 533 161 109 679 931 350 0\n1210 -22 49 747 48 379 167 -825 44 -833 0 408 781 996 843 1072 1041 1079 567 1047 565 8 1088 680 1207 193 686 120 914 442 46 139 69 467 618 130 156 335 1057 642 582 820 716 711 11 380 646 956 858 32 183 257 0\n1211 -14 -112 316 -296 317 -833 0 781 996 1072 1041 1079 843 1016 1092 1100 1124 1028 840 1094 1101 8 1088 680 1207 193 686 120 1008 736 409 656 1058 550 73 308 914 442 46 1155 448 481 692 394 1084 675 441 149 62 136 174 1018 111 256 36 1146 452 241 851 895 108 475 734 916 188 0\n1212 -786 14 6 48 379 167 30 -825 44 29 -833 0 843 996 567 1047 1207 96 316 193 686 442 723 713 119 467 618 937 130 335 1057 1210 642 820 716 711 987 380 655 956 0\n1213 -22 48 379 167 30 -825 44 29 -833 0 996 843 567 1047 1207 193 686 442 467 618 130 335 1057 642 820 699 716 711 937 380 1210 956 987 655 0\n1214 134 -788 131 132 166 163 0 1107 1085 1140 886 896 145 0\n1215 -134 30 -20 -833 0 996 1072 1041 1079 843 1016 1092 1100 1124 408 1047 822 620 515 1024 1119 8 1088 680 1207 193 686 120 1008 736 409 656 88 947 757 914 1073 429 444 579 605 166 446 921 937 989 1209 242 0\n1216 -241 6 30 -20 -833 0 1047 620 515 1024 1119 989 1209 242 0\n1217 -31 -177 -48 379 176 -373 -20 -833 0 1099 1107 1023 1081 1049 822 996 1072 1041 1079 843 1016 1092 1100 1124 1101 1091 781 565 8 1088 680 1207 193 686 120 1008 736 409 656 594 519 944 643 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 524 44 993 485 388 866 124 1058 177 242 814 660 502 1002 293 784 573 582 396 639 11 1141 340 410 252 750 498 988 126 66 1131 690 560 0\n1218 -223 747 79 112 379 276 -212 -833 0 996 1072 1041 1079 843 1016 1092 1100 1124 1028 781 565 225 408 285 8 1088 680 1207 193 686 120 1008 736 409 656 1058 550 73 308 914 570 502 681 293 582 11 176 529 646 734 628 858 183 218 224 951 167 292 326 300 452 506 562 0\n1219 251 223 335 -48 379 176 -373 -20 -833 0 1099 1107 1023 1081 1049 996 1072 1041 1079 843 1016 1092 1100 565 408 822 1124 8 1088 680 1207 193 686 120 1008 736 409 656 594 519 944 643 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 524 44 993 485 388 124 588 1135 535 177 914 573 582 639 11 646 232 224 604 791 126 1131 158 296 560 322 663 690 886 785 66 1019 0\n1220 288 224 223 6 70 379 176 134 163 166 168 132 -833 0 706 839 1072 1041 1079 843 1016 1092 1100 996 822 990 1124 252 8 1088 680 1207 193 686 120 1008 736 409 656 594 519 643 442 782 476 96 316 602 414 54 610 378 165 1058 177 914 340 646 410 750 232 101 498 988 1120 379 126 172 431 1131 158 214 994 663 168 785 150 67 115 0\n1221 -787 379 253 368 -373 -20 -833 0 781 1072 1041 1079 1016 1092 1124 408 1099 1107 397 1023 1081 1049 822 843 996 706 490 186 565 1096 1068 1100 944 417 684 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 215 1128 685 1045 654 890 8 1155 2 190 1088 524 44 993 485 388 124 733 680 193 686 120 1008 736 409 656 88 947 757 914 1073 429 177 442 46 897 175 971 238 1114 231 449 920 870 280 132 255 478 1216 937 606 921 178 1031 1217 987 1218 1219 462 520 1089 41 826 679 486 1134 545 1220 11 1069 375 844 639 1040 730 566 586 616 228 916 0\n1222 379 253 -381 -373 -20 -833 0 781 1072 1041 1079 1016 1092 1100 1124 1099 1107 1023 1081 1049 822 843 996 408 490 1014 684 384 721 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 8 1155 2 993 485 388 124 1088 680 193 686 120 1008 736 409 656 177 442 46 897 175 594 519 1214 1221 544 723 280 470 920 870 1213 313 626 19 1211 713 0\n1223 -786 760 14 6 -112 30 35 -47 0 781 843 996 1096 1118 96 316 442 46 713 1074 618 268 310 156 696 573 639 0\n1224 -198 -112 -379 -381 -373 -20 -833 0 1047 1099 1107 408 1072 1041 1079 1016 1092 1100 1124 1096 1023 1081 397 843 996 490 565 822 804 891 1098 371 1049 1093 1108 1101 1207 96 316 620 215 733 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 8 1155 2 449 313 626 1211 1066 1114 971 1088 680 193 686 120 1008 736 409 19 1115 865 187 438 1014 684 384 721 1215 766 1067 1128 654 524 44 993 485 388 124 515 849 280 648 37 410 11 375 1223 544 146 1214 166 661 519 446 572 391 254 769 362 592 202 889 568 895 916 70 344 623 108 168 1043 290 457 994 245 540 0\n1225 -112 -379 -381 -373 -20 -833 0 1072 1041 1079 1016 1092 1100 1124 1023 1081 996 408 822 1107 1098 804 891 1049 1093 1108 843 1099 1115 865 187 438 1014 684 384 721 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 8 1088 524 44 993 485 388 124 849 680 193 686 120 1008 736 409 19 449 637 1216 1114 937 971 1224 723 833 544 166 619 661 1214 446 606 856 572 519 729 254 769 325 202 568 1012 344 623 380 168 328 673 797 563 22 211 267 80 0\n1226 -323 14 151 -381 222 172 355 166 168 148 175 0 408 804 891 1049 1093 1108 843 1099 1014 684 384 721 4 254 769 572 568 623 1077 18 673 168 1043 1054 994 563 20 158 211 399 80 811 0\n1227 -68 773 30 29 -833 0 839 996 1072 1041 1079 843 1016 1092 1100 1124 1034 8 1088 680 1207 193 686 120 1008 736 409 442 782 53 472 844 265 1069 750 340 0\n1228 -4 -772 -177 112 93 -833 0 996 1072 1041 1079 843 1016 1092 1100 1124 1153 8 1088 680 1207 193 686 120 1008 736 409 570 85 495 541 0\n1229 -69 189 61 125 168 -185 0 346 545 486 1134 326 0\n1230 253 -381 -373 -20 -833 0 781 1072 1041 1079 1016 1092 1100 1124 1047 1099 1107 1023 1081 1049 822 843 996 408 490 1027 706 1101 1091 1014 684 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 906 8 1155 2 190 1088 524 44 993 485 388 866 124 515 64 849 680 193 686 120 1008 736 409 656 88 947 757 914 1073 429 177 442 46 897 175 139 69 417 1222 187 1115 438 671 1225 870 132 255 470 280 298 478 723 448 1216 937 1226 519 1214 544 971 238 231 921 1227 1002 784 396 1141 252 750 1228 1229 1040 100 566 219 1129 835 0\n1231 -381 -373 -20 -833 0 1072 1041 1079 1016 1092 1100 1124 1099 1107 1023 1081 1049 822 843 996 408 781 839 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 8 1155 2 993 485 388 124 1088 680 193 686 120 1008 736 409 656 177 914 442 46 897 175 384 1014 721 684 1230 89 208 879 470 920 300 870 1114 626 19 1225 971 1211 594 1212 519 544 1214 0\n1232 -142 240 325 -294 -833 0 1072 1079 843 1016 1092 1100 1124 996 1041 839 8 1088 680 1207 193 686 120 1008 736 409 656 1058 570 158 214 994 466 353 946 920 71 1114 461 114 304 755 0\n1233 -112 -783 -296 -786 131 142 188 133 189 134 30 166 132 -833 0 781 1072 1041 1079 1016 1092 1124 843 996 285 1100 167 8 1155 1207 96 316 602 414 2 1088 680 193 686 120 1008 736 409 177 442 46 19 1211 713 618 898 268 156 488 992 876 234 413 640 0\n1234 187 334 131 142 188 134 163 166 132 -833 0 996 843 1072 1041 1079 1080 1118 1207 8 1088 680 193 686 120 177 416 1131 830 126 31 0\n1235 232 -786 131 -373 -20 -833 0 781 1099 1107 1023 1081 1049 839 1072 1041 1079 1016 1092 1100 1124 822 843 996 285 1207 96 316 717 963 602 414 8 1088 680 193 686 120 1008 736 409 656 1231 104 1155 2 345 208 1232 1060 1024 1119 632 999 131 869 1051 766 668 773 561 470 10 791 289 896 469 620 695 372 358 744 1208 382 1215 1128 654 190 524 44 993 485 388 124 1058 177 442 46 897 175 41 826 167 386 824 813 1233 870 35 684 486 466 662 1234 643 539 1115 312 865 0\n1236 -232 -373 -20 -833 0 781 1072 1041 1079 1047 1023 1081 1049 822 843 996 839 397 1096 1068 1100 8 1155 1207 96 316 717 963 602 414 2 1231 345 208 470 155 251 926 1024 1119 632 999 131 869 10 1060 620 515 64 215 1088 680 193 686 120 177 442 46 897 175 49 462 1055 951 876 533 626 1035 449 35 870 0\n1237 131 787 -373 -20 -833 0 1099 1107 1023 1081 1049 822 843 996 1236 1207 620 96 316 717 963 602 1024 1119 632 999 131 695 414 1060 372 869 1051 358 744 1208 382 1215 1128 654 993 485 388 124 1214 1235 544 0\n1238 -131 -373 -20 -833 0 1047 1099 1107 1023 1081 1049 822 1016 1092 1100 1124 408 996 843 1072 1041 1079 781 804 891 285 1093 1108 8 1088 524 1236 826 1134 545 680 1207 193 686 120 914 1073 1008 736 409 656 88 3 360 1155 96 316 717 963 602 414 2 1231 345 294 885 104 896 1024 1119 632 999 131 869 1051 906 1128 620 993 485 388 124 515 64 849 139 69 81 519 4 254 743 769 904 572 391 202 438 568 638 199 25 844 18 219 737 715 684 309 1037 227 0\n1239 -373 -20 -833 0 781 996 1072 1041 1079 1016 1092 1100 1124 1099 1107 822 843 1049 1081 1023 839 285 620 993 485 388 124 1024 1119 8 1088 680 1207 193 686 120 1008 736 409 656 1058 177 442 46 897 96 316 1155 175 524 717 44 963 602 414 632 1060 2 999 372 190 131 695 869 1051 1128 358 766 654 744 668 1208 382 1215 1231 469 104 10 345 791 208 773 470 561 1232 1236 41 826 167 386 1238 1237 971 1114 449 920 870 466 35 1234 486 643 539 662 1115 312 865 0\n1240 -176 131 -20 -833 0 1072 1041 1079 1016 1092 1100 1124 1099 1107 565 397 1137 983 645 1023 1081 1049 839 706 843 996 891 1101 1091 1207 620 96 316 442 782 1239 430 54 414 602 1024 1119 159 1061 131 918 963 83 358 751 402 372 744 1208 382 215 406 685 47 593 125 993 485 388 866 124 8 1088 680 193 686 120 1008 736 409 656 1058 177 1155 684 28 1014 466 559 817 469 791 896 1187 564 211 671 617 1227 386 1002 1189 784 561 396 1141 0\n1241 -808 122 124 125 -48 131 171 -824 163 148 121 0 1118 1093 1108 687 1113 505 809 543 612 194 25 13 0\n1242 -381 -787 131 -20 -833 0 1099 565 397 1016 1092 1100 1124 781 1072 1041 490 983 645 1023 1049 839 843 996 706 186 408 1118 1079 1081 1101 1091 971 238 1207 620 96 316 442 782 1239 430 54 414 602 1024 1119 159 1061 131 918 963 83 358 751 402 372 744 1208 382 8 1088 680 193 686 120 177 46 897 1155 175 1114 449 1240 870 470 280 478 1216 606 178 184 1008 736 409 132 906 125 1186 215 406 685 1128 122 480 672 59 385 827 656 88 947 139 69 384 127 721 671 1227 243 1011 447 0\n1243 316 -787 131 -20 -833 0 1028 1099 565 397 490 983 645 1023 1081 1049 706 1016 1092 1100 1124 408 781 996 843 1072 1041 1079 839 225 840 1094 1207 8 1088 680 193 686 120 177 442 46 897 1155 175 971 1114 449 1240 870 470 208 1242 345 209 562 719 251 926 914 1073 429 1008 736 409 656 88 947 238 231 757 620 96 316 782 1239 430 54 414 602 1024 1119 159 1061 131 918 963 83 358 751 402 372 744 1208 382 280 478 1216 937 921 1031 500 906 125 1186 215 122 406 480 672 59 827 849 1058 550 73 308 386 1241 777 62 136 174 703 256 368 36 1146 326 108 734 452 475 1143 0\n1244 -787 131 -20 -833 0 781 1072 1041 1079 1016 1092 1100 1124 1099 565 397 983 1023 1081 1049 839 706 843 996 645 1105 1091 1118 1240 1207 96 316 442 782 1239 430 54 414 602 963 83 906 1024 1119 159 1061 131 918 751 402 125 620 358 372 744 1208 382 1186 215 122 406 480 672 59 385 827 8 1088 680 193 686 120 1008 736 409 177 46 897 1155 175 971 1114 449 870 132 1243 617 97 1059 447 880 194 0\n1245 -788 131 -20 -833 0 1072 1041 1079 1016 1092 1100 1099 1107 565 397 983 645 1023 1081 1049 839 706 843 996 822 1102 891 1118 1124 1240 1207 620 96 316 442 782 1239 430 54 414 602 1024 1119 159 1061 131 918 963 83 358 751 402 372 744 1208 382 1215 906 125 1186 215 122 406 480 672 827 993 485 388 124 8 1088 680 193 686 120 1008 736 409 656 1058 912 146 1140 166 896 207 817 431 44 295 0\n1246 179 131 -20 -833 0 1072 1041 1079 1016 1092 1100 565 397 645 490 839 706 996 843 1023 1081 1049 983 1118 1124 1024 1119 1207 96 316 442 782 1239 430 54 414 602 159 1061 131 751 402 8 1088 680 1240 14 1244 1245 544 723 280 195 986 162 626 386 963 83 766 37 561 906 918 125 620 358 372 744 1208 382 1186 215 122 406 480 672 827 193 686 120 1008 736 409 656 1058 912 194 295 643 539 44 128 1115 1144 865 791 312 0\n1247 -179 373 148 376 0 822 1093 1108 13 431 78 305 724 568 18 638 25 0\n1248 -341 161 343 -379 -323 171 -824 163 -358 175 0 891 233 667 769 16 235 887 747 972 324 886 72 721 44 684 168 20 270 0\n1249 -20 -833 0 839 996 1072 1041 1079 1016 1092 1100 1124 1027 371 397 1047 1099 1107 706 843 645 1049 1081 1023 983 565 804 891 1102 1093 1108 408 8 1088 680 1207 193 686 120 1008 736 409 656 1058 342 116 88 947 96 316 442 782 139 69 1024 535 620 849 1119 215 993 515 122 485 588 64 388 1135 124 1239 430 54 414 602 159 963 1061 83 131 358 906 751 918 827 402 406 125 372 480 744 672 1208 382 1186 1247 1246 81 519 254 594 743 769 202 889 185 438 568 908 671 865 386 1227 219 40 336 85 1141 561 1248 638 425 25 896 18 1054 737 20 684 1149 735 925 224 312 791 0\n1250 -833 0 1079 1041 1072 1101 996 1097 843 1049 1081 1023 8 1088 680 1207 193 96 686 316 120 1249 204 212 153 494 306 260 164 131 1044 1178 602 0\n1251 -148 0 1097 996 1049 1081 1023 1124 1100 1092 1016 1079 1041 1072 1086 1056 1034 843 21 212 1020 153 314 306 260 1009 131 409 1022 1070 1178 510 374 765 602 998 1013 1044 1112 647 120 801 581 118 7 552 0\n1252 20 0 1251 1101 204 0\n1253 462 0 1252 1024 0\n1254 -154 0 1252 843 535 0\n1255 212 0 1252 620 0\n1256 469 0 1252 1138 0\n1257 -29 0 1253 1119 0\n1258 -227 0 1255 397 215 0\n1259 -218 0 1255 993 0\n1260 -217 0 1255 1047 515 0\n1261 -822 0 1258 122 0\n1262 346 0 1259 1099 485 0\n1263 -819 0 1259 588 0\n1264 -25 0 1260 64 0\n1265 -324 0 1262 1107 388 0\n1266 -340 0 1262 1147 0\n1267 821 0 1263 1135 0\n1268 -132 0 1265 124 0\n1269 -688 364 0 1049 1257 1081 1023 996 1252 843 983 658 131 249 751 393 831 402 103 602 766 609 1067 0\n1270 -254 184 175 0 781 1086 1056 1034 1079 1041 1072 996 843 46 1142 442 722 7 120 87 829 0\n1271 184 175 0 996 843 706 1250 1270 691 512 657 142 1026 914 590 575 263 686 193 0\n1272 -342 343 0 843 1016 1092 1100 1124 996 1252 1266 800 832 69 1269 1148 314 1009 409 510 998 1271 0\n1273 343 152 149 0 1093 1251 1108 438 25 18 1272 0\n1274 -93 171 131 179 187 0 1252 565 1118 1261 751 827 406 194 480 672 0\n1275 -157 -185 184 0 996 1256 1079 1041 1072 1252 843 1271 143 189 1030 55 823 772 922 93 287 390 602 120 1112 799 552 0\n1276 364 184 0 1252 1124 1100 1092 1016 1049 1257 1081 1023 996 843 983 1271 143 189 1269 1148 314 1009 409 1275 131 249 751 831 402 602 766 609 1067 0\n1277 344 149 0 408 1266 1265 1049 1257 1081 1023 565 1261 1252 843 996 1124 1100 1092 1016 1093 1251 1108 1118 1086 186 568 1273 187 705 359 643 680 379 1271 69 143 139 189 273 1276 1051 832 913 869 18 605 131 25 249 751 827 831 406 602 480 95 672 422 393 1148 314 1009 409 1010 13 656 689 594 760 519 446 585 178 158 43 0\n1278 187 190 134 166 179 -93 131 0 1252 565 1261 1118 1086 1137 751 406 480 672 827 194 585 493 158 201 0\n1279 -187 149 0 408 492 643 1273 187 0\n1280 352 56 772 -122 135 143 351 134 -827 44 53 172 133 108 157 131 0 1254 1267 1252 1034 1257 1268 1124 455 735 671 865 750 1152 830 960 383 915 1186 265 684 69 1121 348 0\n1281 166 -93 149 0 667 996 983 565 1258 891 567 1266 1265 1093 1108 1137 1100 995 1099 1251 990 1079 1254 1267 843 1277 769 751 406 685 806 896 1128 402 372 125 249 831 210 1279 974 791 519 403 888 666 602 609 569 226 1067 53 1 622 766 744 832 913 984 18 605 273 1278 13 431 25 542 1120 957 528 184 735 947 694 441 149 261 230 1018 340 549 1053 722 1280 127 469 1154 170 510 830 998 915 1271 69 0\n1282 -93 149 0 1016 1092 1100 1124 843 996 1252 1281 189 103 143 393 1271 1148 998 314 510 1009 409 0\n1283 -157 0 1252 996 1124 1100 1092 1016 843 658 869 1148 1051 314 1276 1009 998 409 510 0\n1284 93 0 1283 1023 1081 1257 1049 131 0\n1285 532 0 1284 996 249 0\n1286 285 0 1284 751 0\n1287 -163 0 1284 1252 827 0\n1288 149 0 1284 1282 0\n1289 -102 0 1285 843 831 0\n1290 -290 0 1286 1099 59 0\n1291 -300 0 1286 983 402 0\n1292 -291 0 1286 565 406 0\n1293 341 0 1288 638 0\n1294 -34 0 1288 843 818 0\n1295 -98 0 1290 385 0\n1296 -826 0 1291 372 0\n1297 -823 0 1292 480 0\n1298 355 0 1292 1258 685 0\n1299 -363 0 1293 233 16 0\n1300 -354 0 1293 667 235 0\n1301 824 0 1297 1261 672 0\n1302 -333 0 1298 1137 47 0\n1303 -171 0 1299 493 0\n1304 -162 0 1300 886 0\n1305 226 0 1300 1290 682 0\n1306 -141 0 1302 593 0\n1307 -204 0 1305 397 206 0\n1308 -12 0 1307 530 0\n1309 175 0 1124 1100 1092 1016 1252 1289 996 1284 843 1086 1056 1034 1271 998 510 409 1009 314 1148 393 103 602 316 422 96 7 415 853 0\n1310 367 0 1309 69 0\n1311 609 0 1309 1030 0\n1312 -567 0 1309 843 143 0\n1313 -373 0 1310 1010 0\n1314 -371 0 1310 1299 571 0\n1315 -184 0 1311 843 587 0\n1316 -166 0 1312 996 189 0\n1317 -181 0 1313 689 0\n1318 -179 0 1314 431 0\n1319 364 0 1315 1276 0\n1320 38 0 1316 1289 602 0\n1321 -342 0 1319 1266 832 0\n1322 230 0 1320 609 0\n1323 -172 0 1320 1284 569 0\n1324 -117 0 1320 1309 30 0\n1325 -690 0 1320 1309 95 0\n1326 -150 0 1321 18 0\n1327 -245 0 1322 567 226 0\n1328 -236 0 1322 1067 0\n1329 -689 0 1325 1320 1284 422 0\n1330 -53 0 1327 53 0\n1331 -825 0 1328 1 0\n1332 -688 0 1329 1252 1284 393 0\n1333 827 0 1331 1296 744 0\n1334 -687 0 1332 1252 1148 0\n1335 -686 0 1334 996 843 314 0\n1336 -121 0 1335 1009 0\n1337 185 0 1336 1016 1092 1100 1124 409 0\n1338 377 0 1337 656 0\n1339 -327 0 1338 408 88 0\n1340 -336 0 1338 1058 0\n1341 272 0 1340 1027 342 0\n1342 -144 0 1340 912 0\n1343 -313 0 1341 371 116 0\n1344 131 0 408 1299 1293 1118 1342 1318 1124 1301 1315 1287 1303 1308 1343 1286 1260 1317 1324 1330 1284 1251 1268 1323 1333 1274 574 643 187 972 887 684 721 295 44 128 1144 1150 289 791 813 824 1075 908 894 889 562 1046 749 126 678 855 0\n1345 -89 0 1344 1252 81 0\n1346 323 0 1344 519 0\n1347 -345 0 1346 804 254 0\n1348 -343 0 1346 1339 743 0\n1349 -344 0 1346 891 769 0\n1350 -153 0 1347 202 0\n1351 -151 0 1348 438 0\n1352 -359 0 1348 1293 887 0\n1353 -152 0 1349 568 0\n1354 -360 0 1349 1293 747 0\n1355 -167 0 1352 721 0\n1356 -168 0 1354 44 0\n1357 161 0 1356 1108 1251 1351 1093 1049 1316 1353 1326 1355 623 0\n1358 -77 0 1357 1083 0\n1359 -4 0 1357 1284 336 0\n1360 13 0 1358 1294 1295 1306 1304 802 0\n1361 68 0 1359 1264 1345 1268 1350 219 0\n1362 205 0 1360 533 0\n1363 260 0 1361 844 0\n1364 -232 0 1362 1055 0\n1365 261 0 1363 1286 627 0\n1366 296 0 1364 1354 826 0\n1367 0 1365 1366 1134 0\n"

theorem raw_n8_b7_p01 (word:Fin 8→Fin 3) (base val:Sat.Valuation)
 (h:ModuleOPG1808CNF.LexModel word (lexRot 8) lexPerm base)
 (heq:∀ i,i<OPG1808Cuts.selectorBase 8→(val i↔base i))
 (hc:OPG1808Cuts.CutModel (n:=8) 7 val)
 (hp:word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(1:Fin 3)∧True):False:=by
 have m:=h.toModel
 have bad:=cert_n8_b7_p01 (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 173) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 182) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 191) (val 192) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 201) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 210) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 219) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 228) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 237) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 246) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 255) (val 256) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 265) (val 266) (val 267) (val 268) (val 269) (val 270) (val 271) (val 272) (val 273) (val 274) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 283) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 292) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 301) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 310) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 319) (val 320) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 329) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 336) (val 337) (val 338) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 347) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 356) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 365) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 374) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 383) (val 384) (val 385) (val 386) (val 387) (val 388) (val 389) (val 390) (val 391) (val 392) (val 393) (val 394) (val 395) (val 396) (val 397) (val 398) (val 399) (val 400) (val 401) (val 402) (val 403) (val 404) (val 405) (val 406) (val 407) (val 408) (val 409) (val 410) (val 411) (val 412) (val 413) (val 414) (val 415) (val 416) (val 417) (val 418) (val 419) (val 420) (val 421) (val 422) (val 423) (val 424) (val 425) (val 426) (val 427) (val 428) (val 429) (val 430) (val 431) (val 432) (val 433) (val 434) (val 435) (val 436) (val 437) (val 438) (val 439) (val 440) (val 441) (val 442) (val 443) (val 444) (val 445) (val 446) (val 447) (val 448) (val 449) (val 450) (val 451) (val 452) (val 453) (val 454) (val 455) (val 456) (val 457) (val 458) (val 459) (val 460) (val 461) (val 462) (val 463) (val 464) (val 465) (val 466) (val 467) (val 468) (val 469) (val 470) (val 471) (val 472) (val 473) (val 474) (val 475) (val 476) (val 477) (val 478) (val 479) (val 480) (val 481) (val 482) (val 483) (val 484) (val 485) (val 486) (val 487) (val 488) (val 489) (val 490) (val 491) (val 492) (val 493) (val 494) (val 495) (val 496) (val 497) (val 498) (val 499) (val 500) (val 501) (val 502) (val 503) (val 504) (val 505) (val 506) (val 507) (val 508) (val 509) (val 510) (val 511) (val 512) (val 513) (val 514) (val 515) (val 516) (val 517) (val 518) (val 519) (val 520) (val 521) (val 522) (val 523) (val 524) (val 525) (val 526) (val 527) (val 528) (val 529) (val 530) (val 531) (val 532) (val 533) (val 534) (val 535) (val 536) (val 537) (val 538) (val 539) (val 540) (val 541) (val 542) (val 543) (val 544) (val 545) (val 546) (val 547) (val 548) (val 549) (val 550) (val 551) (val 552) (val 553) (val 554) (val 555) (val 556) (val 557) (val 558) (val 559) (val 560) (val 561) (val 562) (val 563) (val 564) (val 565) (val 566) (val 567) (val 568) (val 569) (val 570) (val 571) (val 572) (val 573) (val 574) (val 575) (val 576) (val 577) (val 578) (val 579) (val 580) (val 581) (val 582) (val 583) (val 584) (val 585) (val 586) (val 587) (val 588) (val 589) (val 590) (val 591) (val 592) (val 593) (val 594) (val 595) (val 596) (val 597) (val 598) (val 599) (val 600) (val 601) (val 602) (val 603) (val 604) (val 605) (val 606) (val 607) (val 608) (val 609) (val 610) (val 611) (val 612) (val 613) (val 614) (val 615) (val 616) (val 617) (val 618) (val 619) (val 620) (val 621) (val 622) (val 623) (val 624) (val 625) (val 626) (val 627) (val 628) (val 629) (val 630) (val 631) (val 632) (val 633) (val 634) (val 635) (val 636) (val 637) (val 638) (val 639) (val 640) (val 641) (val 642) (val 643) (val 644) (val 645) (val 646) (val 647) (val 648) (val 649) (val 650) (val 651) (val 652) (val 653) (val 654) (val 655) (val 656) (val 657) (val 658) (val 659) (val 660) (val 661) (val 662) (val 663) (val 664) (val 665) (val 666) (val 667) (val 668) (val 669) (val 670) (val 671) (val 672) (val 673) (val 674) (val 675) (val 676) (val 677) (val 678) (val 679) (val 680) (val 681) (val 682) (val 683) (val 684) (val 685) (val 686) (val 687) (val 688) (val 689) (val 690) (val 691) (val 692) (val 693) (val 694) (val 695) (val 696) (val 697) (val 698) (val 699) (val 700) (val 701) (val 702) (val 703) (val 704) (val 705) (val 706) (val 707) (val 708) (val 709) (val 710) (val 711) (val 712) (val 713) (val 714) (val 715) (val 716) (val 717) (val 718) (val 719) (val 720) (val 721) (val 722) (val 723) (val 724) (val 725) (val 726) (val 727) (val 728) (val 729) (val 730) (val 731) (val 732) (val 733) (val 734) (val 735) (val 736) (val 737) (val 738) (val 739) (val 740) (val 741) (val 742) (val 743) (val 744) (val 745) (val 746) (val 747) (val 748) (val 749) (val 750) (val 751) (val 752) (val 753) (val 754) (val 755) (val 756) (val 757) (val 758) (val 759) (val 760) (val 761) (val 762) (val 763) (val 764) (val 765) (val 766) (val 767) (val 768) (val 769) (val 770) (val 771) (val 772) (val 773) (val 774) (val 775) (val 776) (val 777) (val 778) (val 779) (val 780) (val 781) (val 782) (val 783) (val 784) (val 785) (val 786) (val 787) (val 788) (val 789) (val 790) (val 791) (val 792) (val 793) (val 794) (val 795) (val 796) (val 797) (val 798) (val 799) (val 800) (val 801) (val 802) (val 803) (val 804) (val 805) (val 806) (val 807) (val 808) (val 809) (val 810) (val 811) (val 812) (val 813) (val 814) (val 815) (val 816) (val 817) (val 818) (val 819) (val 820) (val 821) (val 822) (val 823) (val 824) (val 825) (val 826) (val 827) (val 828) (val 829) (val 830) (val 831) (val 832)
 exact (Or.elim bad
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 1 4 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 35 2 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 43 1 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 5) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 1) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 33 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 35 0 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 1 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 43 4 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 24 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 23 1 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 43 3 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 3) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 21 0 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 1 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 6 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 31 2 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 26 0 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 9 0 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 1) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 23 2 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 0 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 25 0 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 0 2 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 1 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 0) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 26 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 35 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 3) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 29 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 31 1 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 16 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 5) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 6) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 0) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 4) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 31 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 0 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 7 (by decide)) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 21 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 2) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 9 1 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 3) (by decide)) (b))
 (fun b=>(hc.ambient_clause 2 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 12 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 16 0 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 0 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 2 (by decide) 2) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 43 0 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 24 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_conflict_clause 1 1 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 4) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 38 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 19 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 1) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 1 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 0 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 14 0 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 2) (by decide)) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 0) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 36 0 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 21 1 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 1) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 1) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 2) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 0 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.ambient_clause 4 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 39 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 43 2 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 3) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 43 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 6) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.ambient_clause 3 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 43 5 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 31 0 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 43 3 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 6 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 36 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 7) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 0 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 7) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 9 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 36 1 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 5) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 18 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 11 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 41 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 7) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 25 1 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 4) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 2 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 17 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 0 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 1) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 38 0 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 7) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 32 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 2) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 1 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 4) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 27 0 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 2 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 2 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 2) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 6 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 2 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 17 1 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 0 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 23 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 5) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 4 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 25 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 19 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 3) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 17 0 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 43 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 1) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 0 (by decide) 7 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 4) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 29 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 2 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 3 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 5) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 23 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 7) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 20 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 2) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 39 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 0 (by decide)) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 5) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 9 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 0 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 31 3 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 0) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 18 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 0 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 17 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 12 0 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 6) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 27 1 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 25 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 6) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 2) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 1 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 2) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 5) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 12 2 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.ambient_clause 4 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 33 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 21 0 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 4) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 1 1 (hp.2.1)) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 0 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 12 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 3 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 27 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 43 4 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 7) (by decide)) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 4) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 11 0 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 7 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 35 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 4) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 23 0 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 0 (by decide)) (by decide)) (b.1) (b.2))))))
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
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 2 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 1 (by decide) 7 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 6) (by decide)) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 12 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 14 1 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 43 1 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 14 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 4) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 2 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))))
end OPG1808CutCertificates
end

end Cut8Prefix01Packet

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
    (hprefix1 : color (1:Fin 8) (finRotate 8 (1:Fin 8)) = (1:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  exact Cut8Prefix01Packet.OPG1808PhysicalPrefix.predecessor_reachable_of_cut_exclusion
    (fun word ↦ word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(1:Fin 3)∧True) Cut8Prefix01Packet.OPG1808CutCertificates.raw_n8_b7_p01
    D color htournament hnoRainbow hcycle hminimal ⟨hprefix0,hprefix1,True.intro⟩
