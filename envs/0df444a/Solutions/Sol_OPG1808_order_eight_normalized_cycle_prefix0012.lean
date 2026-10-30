-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix0012
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:05:53.56369+00:00
-- url     : https://prove2.me/submissions/508fd2e6-0a4d-4886-a665-9ef54a1a6c9e

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

namespace Cut8Prefix0012CompactV3Packet

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
lrat_proof cert_n8_b7_p0012
 "p cnf 471 1204\n-1 -56 0\n-1 -112 0\n-57 -113 0\n2 21 58 77 114 132 0\n-2 -58 0\n-2 -77 0\n-2 -114 0\n-58 -77 0\n-58 -114 0\n3 28 59 84 115 139 0\n-3 -28 0\n-3 -59 0\n-3 -139 0\n-28 -59 0\n-59 -84 0\n-59 -115 0\n-59 -139 0\n-115 -139 0\n4 35 60 91 116 146 0\n-4 -35 0\n-4 -91 0\n-35 -60 0\n-35 -91 0\n-35 -116 0\n-35 -146 0\n-60 -91 0\n-116 -146 0\n5 42 61 98 117 153 0\n-5 -42 0\n-42 -153 0\n-98 -153 0\n-117 -153 0\n6 49 62 105 118 160 0\n-105 -160 0\n-8 -64 0\n-8 -120 0\n9 22 65 78 121 133 0\n-9 -65 0\n-9 -121 0\n-65 -121 0\n10 29 66 85 122 140 0\n-10 -29 0\n-10 -66 0\n-29 -66 0\n-29 -122 0\n-29 -140 0\n-66 -122 0\n-66 -140 0\n-122 -140 0\n11 36 67 92 123 147 0\n-11 -36 0\n-36 -67 0\n-36 -123 0\n-36 -147 0\n-67 -92 0\n-67 -123 0\n-67 -147 0\n-123 -147 0\n12 43 68 99 124 154 0\n-12 -154 0\n-43 -154 0\n-68 -99 0\n-68 -154 0\n-99 -154 0\n-124 -154 0\n13 50 69 106 125 161 0\n-50 -106 0\n-50 -125 0\n-50 -161 0\n-106 -125 0\n-106 -161 0\n-125 -161 0\n-16 -72 0\n-72 -127 0\n17 30 73 86 128 141 0\n-17 -73 0\n18 37 74 93 129 148 0\n-18 -37 0\n-18 -129 0\n-37 -74 0\n-37 -93 0\n-37 -129 0\n-74 -93 0\n-74 -129 0\n-93 -129 0\n19 44 75 100 130 155 0\n-19 -100 0\n20 51 76 107 131 162 0\n-51 -107 0\n-24 -135 0\n-80 -135 0\n25 38 81 94 136 149 0\n-25 -81 0\n-38 -81 0\n-81 -94 0\n-81 -136 0\n-94 -136 0\n26 45 82 101 137 156 0\n-82 -101 0\n27 52 83 108 138 163 0\n-52 -83 0\n-52 -138 0\n-83 -108 0\n-83 -138 0\n-138 -163 0\n32 39 88 95 143 150 0\n-32 -88 0\n-32 -143 0\n33 46 89 102 144 157 0\n-33 -89 0\n-33 -102 0\n-33 -144 0\n-46 -144 0\n-89 -144 0\n-144 -157 0\n34 53 90 109 145 164 0\n-34 -53 0\n-34 -90 0\n-34 -145 0\n-53 -145 0\n-90 -145 0\n-109 -145 0\n-145 -164 0\n40 47 96 103 151 158 0\n-40 -96 0\n-40 -151 0\n-96 -151 0\n41 54 97 110 152 165 0\n-41 -97 0\n-41 -152 0\n-54 -152 0\n-97 -110 0\n-97 -152 0\n-97 -165 0\n-152 -165 0\n48 55 104 111 159 166 0\n-48 -104 0\n-48 -159 0\n-104 -159 0\n-1 167 0\n-2 169 0\n-3 170 0\n-4 171 0\n-5 172 0\n-6 173 0\n-7 174 0\n-8 175 0\n-9 176 0\n-10 177 0\n-11 178 0\n-12 179 0\n-13 180 0\n-14 181 0\n-15 182 0\n-17 184 0\n-18 185 0\n-19 186 0\n-20 187 0\n-21 188 0\n-22 189 0\n-23 190 0\n-25 191 0\n-26 192 0\n-27 193 0\n-28 194 0\n-29 195 0\n-31 197 0\n-32 198 0\n-33 199 0\n-34 200 0\n-35 201 0\n-36 202 0\n-37 203 0\n-38 204 0\n-39 205 0\n-40 206 0\n-41 207 0\n-42 208 0\n-43 209 0\n-44 210 0\n-45 211 0\n-46 212 0\n-47 213 0\n-48 214 0\n-50 216 0\n-51 217 0\n-52 218 0\n-53 219 0\n-54 220 0\n-55 221 0\n-167 -175 168 0\n-167 -176 169 0\n-167 -177 170 0\n-167 -178 171 0\n-167 -180 173 0\n-168 -184 170 0\n-169 -193 173 0\n-170 -198 171 0\n-170 -199 172 0\n-170 -200 173 0\n-171 -204 169 0\n-171 -207 173 0\n-172 -211 169 0\n-172 -212 170 0\n-172 -214 173 0\n-175 -184 177 0\n-175 -185 178 0\n-175 -186 179 0\n-175 -187 180 0\n-176 -192 179 0\n-176 -193 180 0\n-177 -194 174 0\n-177 -198 178 0\n-177 -199 179 0\n-177 -200 180 0\n-178 -201 174 0\n-178 -204 176 0\n-178 -206 179 0\n-178 -207 180 0\n-179 -208 174 0\n-179 -214 180 0\n-181 -167 182 0\n-184 -194 181 0\n-184 -195 182 0\n-184 -198 185 0\n-184 -199 186 0\n-184 -200 187 0\n-185 -201 181 0\n-185 -202 182 0\n-185 -204 183 0\n-185 -206 186 0\n-186 -208 181 0\n-186 -214 187 0\n-188 -168 190 0\n-189 -175 190 0\n-191 -201 188 0\n-191 -202 189 0\n-191 -203 190 0\n-191 -206 192 0\n-192 -208 188 0\n-192 -209 189 0\n-192 -214 193 0\n-193 -216 189 0\n-194 -167 195 0\n-194 -169 197 0\n-195 -176 197 0\n-195 -179 199 0\n-196 -183 197 0\n-198 -201 194 0\n-198 -202 195 0\n-198 -204 197 0\n-198 -206 199 0\n-198 -207 200 0\n-199 -209 195 0\n-199 -211 197 0\n-200 -218 197 0\n-200 -220 198 0\n-201 -167 202 0\n-201 -169 204 0\n-201 -170 205 0\n-202 -176 204 0\n-202 -177 205 0\n-202 -179 206 0\n-203 -184 205 0\n-203 -186 206 0\n-204 -192 206 0\n-206 -212 205 0\n-207 -216 202 0\n-207 -217 203 0\n-207 -219 205 0\n-208 -167 209 0\n-208 -168 210 0\n-208 -169 211 0\n-208 -170 212 0\n-208 -171 213 0\n-209 -175 210 0\n-209 -176 211 0\n-209 -177 212 0\n-209 -178 213 0\n-210 -184 212 0\n-210 -185 213 0\n-211 -191 213 0\n-212 -194 208 0\n-212 -198 213 0\n-212 -200 214 0\n-214 -218 211 0\n-214 -220 213 0\n-215 -171 220 0\n-215 -172 221 0\n-216 -175 217 0\n-216 -176 218 0\n-216 -177 219 0\n-216 -178 220 0\n-216 -179 221 0\n-217 -185 220 0\n-217 -186 221 0\n-218 -191 220 0\n-218 -192 221 0\n-219 -194 215 0\n-219 -196 217 0\n-219 -198 220 0\n-219 -199 221 0\n-220 -201 215 0\n-220 -206 221 0\n-57 223 0\n-58 224 0\n-59 225 0\n-60 226 0\n-61 227 0\n-62 228 0\n-63 229 0\n-65 231 0\n-66 232 0\n-67 233 0\n-68 234 0\n-70 236 0\n-71 237 0\n-72 238 0\n-73 239 0\n-74 240 0\n-75 241 0\n-76 242 0\n-77 243 0\n-78 244 0\n-79 245 0\n-81 247 0\n-82 248 0\n-83 249 0\n-84 250 0\n-85 251 0\n-86 252 0\n-87 253 0\n-88 254 0\n-89 255 0\n-90 256 0\n-91 257 0\n-92 258 0\n-93 259 0\n-94 260 0\n-95 261 0\n-96 262 0\n-97 263 0\n-98 264 0\n-99 265 0\n-100 266 0\n-101 267 0\n-102 268 0\n-103 269 0\n-104 270 0\n-105 271 0\n-106 272 0\n-107 273 0\n-108 274 0\n-109 275 0\n-110 276 0\n-111 277 0\n-222 -235 228 0\n-223 -238 224 0\n-223 -242 228 0\n-224 -247 226 0\n-224 -249 228 0\n-225 -255 227 0\n-225 -256 228 0\n-226 -258 222 0\n-226 -262 227 0\n-226 -263 228 0\n-227 -265 222 0\n-227 -270 228 0\n-230 -236 229 0\n-230 -238 231 0\n-231 -243 229 0\n-231 -247 233 0\n-231 -248 234 0\n-232 -250 229 0\n-232 -254 233 0\n-232 -255 234 0\n-233 -257 229 0\n-233 -259 230 0\n-233 -260 231 0\n-233 -262 234 0\n-234 -264 229 0\n-234 -267 231 0\n-235 -271 229 0\n-235 -273 230 0\n-235 -274 231 0\n-235 -275 232 0\n-238 -243 236 0\n-238 -244 237 0\n-238 -247 240 0\n-239 -250 236 0\n-239 -254 240 0\n-239 -255 241 0\n-240 -258 237 0\n-240 -262 241 0\n-241 -265 237 0\n-242 -272 237 0\n-243 -223 245 0\n-243 -225 246 0\n-247 -257 243 0\n-247 -258 244 0\n-247 -259 245 0\n-247 -262 248 0\n-247 -263 249 0\n-248 -264 243 0\n-248 -265 244 0\n-248 -266 245 0\n-248 -268 246 0\n-248 -270 249 0\n-249 -272 244 0\n-249 -273 245 0\n-249 -275 246 0\n-250 -223 252 0\n-250 -224 253 0\n-250 -226 254 0\n-251 -230 252 0\n-251 -231 253 0\n-251 -233 254 0\n-251 -235 256 0\n-252 -238 253 0\n-254 -259 252 0\n-254 -260 253 0\n-254 -263 256 0\n-255 -264 250 0\n-255 -266 252 0\n-255 -267 253 0\n-255 -270 256 0\n-256 -271 250 0\n-256 -273 252 0\n-256 -274 253 0\n-256 -276 254 0\n-257 -223 259 0\n-257 -225 261 0\n-258 -230 259 0\n-258 -235 263 0\n-259 -236 257 0\n-259 -239 261 0\n-259 -242 263 0\n-260 -243 257 0\n-260 -246 261 0\n-260 -249 263 0\n-262 -264 257 0\n-262 -266 259 0\n-262 -267 260 0\n-262 -268 261 0\n-262 -270 263 0\n-263 -271 257 0\n-263 -273 259 0\n-263 -274 260 0\n-263 -275 261 0\n-264 -223 266 0\n-264 -224 267 0\n-264 -225 268 0\n-264 -226 269 0\n-265 -231 267 0\n-265 -232 268 0\n-265 -233 269 0\n-266 -239 268 0\n-266 -240 269 0\n-266 -242 270 0\n-267 -247 269 0\n-268 -250 264 0\n-268 -251 265 0\n-268 -254 269 0\n-268 -256 270 0\n-270 -272 265 0\n-270 -273 266 0\n-270 -274 267 0\n-270 -275 268 0\n-270 -276 269 0\n-271 -226 276 0\n-271 -227 277 0\n-272 -232 275 0\n-272 -233 276 0\n-272 -234 277 0\n-273 -236 271 0\n-273 -238 274 0\n-273 -239 275 0\n-273 -240 276 0\n-273 -241 277 0\n-274 -243 271 0\n-274 -247 276 0\n-274 -248 277 0\n-275 -250 271 0\n-275 -254 276 0\n-275 -255 277 0\n-276 -259 273 0\n-276 -262 277 0\n-113 279 0\n-114 280 0\n-115 281 0\n-116 282 0\n-117 283 0\n-118 284 0\n-119 285 0\n-121 287 0\n-122 288 0\n-123 289 0\n-124 290 0\n-125 291 0\n-126 293 0\n-128 295 0\n-129 296 0\n-130 297 0\n-131 298 0\n-132 299 0\n-134 301 0\n-135 302 0\n-136 303 0\n-137 304 0\n-138 305 0\n-139 306 0\n-140 307 0\n-141 308 0\n-142 309 0\n-144 311 0\n-145 312 0\n-146 313 0\n-147 314 0\n-148 315 0\n-149 316 0\n-150 317 0\n-151 318 0\n-152 319 0\n-153 320 0\n-154 321 0\n-155 322 0\n-156 323 0\n-157 324 0\n-158 325 0\n-159 326 0\n-160 327 0\n-161 328 0\n-162 329 0\n-163 330 0\n-164 331 0\n-165 332 0\n-166 333 0\n-278 -291 284 0\n-279 -298 284 0\n-280 -300 278 0\n-280 -302 281 0\n-280 -303 282 0\n-280 -304 283 0\n-280 -305 284 0\n-281 -307 278 0\n-281 -311 283 0\n-281 -312 284 0\n-282 -314 278 0\n-282 -318 283 0\n-282 -319 284 0\n-283 -323 280 0\n-283 -326 284 0\n-287 -299 285 0\n-287 -302 288 0\n-287 -303 289 0\n-287 -304 290 0\n-287 -305 291 0\n-288 -306 285 0\n-288 -310 289 0\n-288 -311 290 0\n-288 -312 291 0\n-289 -313 285 0\n-289 -315 286 0\n-289 -318 290 0\n-289 -319 291 0\n-290 -320 285 0\n-291 -327 285 0\n-291 -331 288 0\n-291 -332 289 0\n-292 -278 293 0\n-294 -300 293 0\n-295 -307 293 0\n-295 -311 297 0\n-295 -312 298 0\n-296 -314 293 0\n-296 -318 297 0\n-296 -319 298 0\n-297 -321 293 0\n-298 -328 293 0\n-298 -330 294 0\n-299 -279 301 0\n-300 -286 301 0\n-300 -289 303 0\n-300 -290 304 0\n-302 -306 299 0\n-302 -308 301 0\n-302 -311 304 0\n-302 -312 305 0\n-303 -315 301 0\n-303 -318 304 0\n-303 -319 305 0\n-304 -320 299 0\n-305 -327 299 0\n-305 -329 301 0\n-306 -279 308 0\n-306 -280 309 0\n-306 -282 310 0\n-307 -287 309 0\n-311 -320 306 0\n-311 -321 307 0\n-311 -322 308 0\n-311 -323 309 0\n-312 -327 306 0\n-312 -329 308 0\n-312 -330 309 0\n-312 -332 310 0\n-313 -280 316 0\n-313 -281 317 0\n-314 -287 316 0\n-314 -288 317 0\n-314 -290 318 0\n-314 -291 319 0\n-316 -302 317 0\n-318 -320 313 0\n-318 -321 314 0\n-318 -322 315 0\n-318 -323 316 0\n-318 -324 317 0\n-319 -330 316 0\n-319 -331 317 0\n-320 -282 325 0\n-321 -287 323 0\n-321 -288 324 0\n-321 -289 325 0\n-322 -296 325 0\n-323 -303 325 0\n-323 -305 326 0\n-324 -306 320 0\n-324 -310 325 0\n-324 -312 326 0\n-326 -332 325 0\n-327 -279 329 0\n-327 -280 330 0\n-327 -283 333 0\n-328 -287 330 0\n-328 -288 331 0\n-328 -289 332 0\n-328 -290 333 0\n-330 -300 328 0\n-330 -302 331 0\n-330 -304 333 0\n-331 -311 333 0\n-332 -314 328 0\n-332 -318 333 0\n-173 0\n-228 0\n-284 0\n-174 0\n-229 0\n-285 0\n-182 0\n-237 0\n-293 0\n-190 0\n-245 0\n-301 0\n-197 0\n-253 0\n-309 0\n32 88 143 0\n-205 0\n-261 0\n-317 0\n40 96 151 0\n-213 0\n-269 0\n-325 0\n48 104 159 0\n-221 0\n-277 0\n-333 0\n49 105 160 0\n1 0\n8 0\n72 0\n135 0\n-1 -65 -132 0\n-1 -121 -77 0\n-1 -66 -139 0\n-1 -122 -84 0\n-1 -67 -146 0\n-1 -123 -91 0\n-1 -68 -153 0\n-1 -124 -98 0\n-1 -69 -160 0\n-1 -125 -105 0\n-2 -135 -84 0\n-58 -135 -28 0\n-2 -81 -146 0\n-58 -136 -35 0\n-2 -82 -153 0\n-2 -137 -98 0\n-58 -26 -153 0\n-58 -137 -42 0\n-114 -82 -42 0\n-2 -83 -160 0\n-2 -138 -105 0\n-58 -27 -160 0\n-59 -32 -146 0\n-115 -32 -91 0\n-115 -88 -35 0\n-3 -89 -153 0\n-3 -144 -98 0\n-59 -33 -153 0\n-59 -144 -42 0\n-3 -90 -160 0\n-3 -145 -105 0\n-59 -34 -160 0\n-115 -34 -105 0\n-4 -96 -153 0\n-4 -151 -98 0\n-60 -40 -153 0\n-116 -40 -98 0\n-116 -96 -42 0\n-4 -97 -160 0\n-4 -152 -105 0\n-60 -41 -160 0\n-5 -104 -160 0\n-5 -159 -105 0\n-61 -48 -160 0\n-8 -72 -133 0\n-8 -73 -140 0\n-8 -74 -147 0\n-8 -129 -92 0\n-8 -75 -154 0\n-8 -76 -161 0\n-8 -131 -106 0\n-9 -135 -85 0\n-65 -135 -29 0\n-9 -81 -147 0\n-65 -136 -36 0\n-9 -82 -154 0\n-9 -83 -161 0\n-65 -138 -50 0\n-121 -27 -106 0\n-10 -88 -147 0\n-66 -32 -147 0\n-122 -32 -92 0\n-122 -88 -36 0\n-10 -89 -154 0\n-10 -144 -99 0\n-66 -33 -154 0\n-10 -90 -161 0\n-10 -145 -106 0\n-66 -34 -161 0\n-66 -145 -50 0\n-122 -34 -106 0\n-122 -90 -50 0\n-11 -96 -154 0\n-67 -40 -154 0\n-123 -96 -43 0\n-67 -152 -50 0\n-68 -48 -161 0\n-124 -48 -106 0\n-72 -135 -30 0\n-72 -136 -37 0\n-72 -138 -51 0\n-128 -32 -93 0\n-73 -144 -44 0\n-17 -145 -107 0\n-73 -145 -51 0\n-128 -34 -107 0\n-129 -96 -44 0\n-18 -152 -107 0\n-74 -152 -51 0\n-130 -48 -107 0\n-135 -32 -94 0\n-135 -88 -38 0\n-135 -33 -101 0\n-135 -89 -45 0\n-135 -34 -108 0\n-135 -90 -52 0\n-136 -96 -45 0\n-136 -97 -52 0\n-82 -48 -163 0\n-137 -104 -52 0\n-32 -151 -102 0\n-88 -151 -46 0\n-32 -97 -164 0\n-32 -152 -109 0\n-88 -152 -53 0\n-33 -104 -164 0\n-144 -48 -109 0\n-144 -104 -53 0\n-40 -104 -165 0\n-96 -48 -165 0\n-151 -48 -110 0\n-151 -104 -54 0\n-1 -135 334 0\n-334 -8 -143 335 0\n-335 -72 -40 336 0\n-335 -72 -151 0\n-336 -135 -48 0\n-336 -135 -104 337 0\n-336 -135 -159 0\n-337 -88 -160 0\n-337 -143 -160 0\n-1 -135 338 0\n-338 -8 -143 339 0\n-339 -72 -96 340 0\n-340 -135 -48 341 0\n-340 -135 -104 0\n-340 -135 -159 0\n-341 -143 -105 0\n-341 -143 -160 0\n-1 -88 342 0\n-342 -8 -96 343 0\n-343 -72 -104 0\n-1 -88 344 0\n-344 -8 -96 345 0\n-345 -72 -104 0\n-345 -72 -159 346 0\n-346 -135 -105 0\n-1 -40 347 0\n-347 -8 -48 348 0\n-348 -72 -105 349 0\n-349 -135 -1 0\n-1 -40 350 0\n-350 -8 -48 351 0\n-351 -72 -160 352 0\n-352 -135 -1 0\n-1 -104 353 0\n-353 -8 -105 354 0\n-354 -72 -1 355 0\n-355 -135 -8 0\n-1 -159 356 0\n-356 -8 -160 357 0\n-357 -72 -1 358 0\n-358 -135 -8 0\n-1 -49 359 0\n-359 -8 -1 360 0\n-360 -72 -8 0\n169 224 280 0\n170 225 281 0\n171 226 282 0\n172 227 283 0\n176 231 287 0\n177 232 288 0\n178 233 289 0\n179 234 290 0\n180 235 291 0\n184 239 295 0\n185 240 296 0\n186 241 297 0\n187 242 298 0\n181 236 292 0\n191 247 303 0\n193 249 305 0\n188 243 299 0\n189 244 300 0\n199 255 311 0\n200 256 312 0\n194 250 306 0\n195 251 307 0\n196 252 308 0\n207 263 319 0\n201 257 313 0\n202 258 314 0\n203 259 315 0\n204 260 316 0\n208 264 320 0\n211 267 323 0\n212 268 324 0\n216 272 328 0\n217 273 329 0\n218 274 330 0\n219 275 331 0\n220 276 332 0\n361 362 363 0\n-361 9 16 0\n-362 231 0\n-363 287 0\n364 365 366 0\n-364 191 0\n-365 247 0\n-365 80 81 0\n-366 303 0\n-366 136 143 0\n367 368 369 0\n-367 199 0\n-367 33 40 0\n-368 255 0\n-368 88 89 0\n-369 311 0\n-369 143 144 0\n370 371 372 0\n-370 207 0\n-370 40 41 0\n-371 263 0\n-371 96 97 0\n-371 97 104 0\n-372 319 0\n-372 152 159 0\n373 374 375 0\n-373 208 0\n-373 42 49 0\n-374 264 0\n-374 104 98 0\n-374 98 105 0\n-375 320 0\n-375 159 153 0\n-375 153 160 0\n376 377 378 0\n-376 216 0\n-376 49 50 0\n-377 272 0\n-377 106 56 0\n-378 328 0\n-378 161 112 0\n379 380 381 0\n-379 169 0\n-379 2 9 16 0\n-380 224 0\n-380 56 57 58 0\n-381 280 0\n-381 112 114 126 127 0\n382 383 384 0\n-382 177 0\n-382 10 17 24 0\n-383 64 66 79 80 0\n-384 288 0\n-384 120 121 122 0\n385 386 387 0\n-385 185 0\n-385 16 17 18 0\n-386 240 0\n-386 73 74 80 81 0\n-386 74 81 88 0\n-387 296 0\n-387 127 129 142 143 0\n388 389 390 0\n-388 192 0\n-389 248 0\n-389 80 81 82 0\n-390 304 0\n-390 136 137 143 144 0\n391 392 393 0\n-391 200 0\n-391 33 34 40 41 0\n-391 32 34 47 48 0\n-391 34 41 48 0\n-392 256 0\n-392 88 89 90 0\n-392 89 90 96 97 0\n-392 88 90 103 104 0\n-393 312 0\n-393 143 144 145 0\n-393 143 145 158 159 0\n394 395 396 0\n-394 201 0\n-394 40 35 55 49 0\n-394 35 42 49 0\n-395 257 0\n-395 97 91 104 98 0\n-395 96 91 111 105 0\n-395 91 98 105 0\n-396 313 0\n-396 151 152 146 0\n-396 152 146 159 153 0\n397 398 399 0\n-397 209 0\n-397 48 42 43 0\n-398 265 0\n-398 99 106 56 0\n-399 159 154 118 112 0\n400 401 402 0\n-400 217 0\n-400 49 50 51 0\n-401 273 0\n-401 105 107 63 64 0\n-401 107 57 64 0\n-402 329 0\n403 404 405 0\n-403 170 0\n-404 56 57 59 78 79 80 0\n-405 281 0\n406 407 408 0\n-406 178 0\n-406 10 11 17 18 24 25 0\n-407 233 0\n-407 64 66 67 79 80 81 0\n-407 64 67 79 81 86 88 0\n-408 289 0\n-408 120 121 122 123 0\n-408 120 121 123 141 142 143 0\n409 410 411 0\n-409 186 0\n-410 241 0\n-410 73 74 75 80 81 82 0\n-410 75 82 89 96 0\n-411 297 0\n-411 127 129 130 142 143 144 0\n412 413 414 0\n-412 193 0\n-412 24 26 27 39 40 41 0\n-412 24 25 27 46 47 48 0\n-412 24 27 39 41 46 48 0\n-413 249 0\n-413 80 82 83 95 96 97 0\n-414 305 0\n-414 138 145 152 159 0\n415 416 417 0\n-415 194 0\n-415 32 34 28 47 48 42 0\n-415 32 33 28 54 55 49 0\n-415 32 28 47 42 54 49 0\n-415 28 35 42 49 0\n-416 250 0\n-416 88 89 90 84 0\n-416 89 90 84 96 97 91 0\n-416 88 90 84 103 104 98 0\n-416 90 84 97 91 104 98 0\n-416 88 89 84 110 111 105 0\n-416 89 84 96 91 111 105 0\n-416 88 84 103 98 110 105 0\n-416 84 91 98 105 0\n-417 306 0\n-417 143 144 145 139 0\n-417 143 145 139 158 159 153 0\n-417 143 139 158 153 165 160 0\n418 419 420 0\n-418 202 0\n-418 40 41 35 36 0\n-419 258 0\n-420 314 0\n-420 151 152 147 117 118 112 0\n-420 152 147 159 154 118 112 0\n421 422 423 0\n-421 48 42 43 44 0\n-422 266 0\n-422 98 100 105 107 63 64 0\n-423 322 0\n424 425 426 0\n-424 218 0\n-424 49 50 52 14 15 16 0\n-425 274 0\n-425 105 106 107 108 0\n-425 106 107 108 56 57 58 0\n-425 105 107 108 63 64 65 0\n-426 330 0\n-426 163 114 121 127 0\n427 428 429 0\n-427 171 0\n-427 3 4 10 11 17 18 24 25 0\n-427 4 11 18 25 32 0\n-428 226 0\n-428 56 60 71 74 78 81 85 88 0\n-429 282 0\n-429 112 113 114 116 140 141 142 143 0\n430 431 432 0\n-430 179 0\n-431 234 0\n-431 64 66 67 68 79 80 81 82 0\n-431 67 68 74 75 81 82 88 89 0\n-432 290 0\n-432 120 121 122 123 124 0\n-432 120 121 123 124 141 142 143 144 0\n433 434 435 0\n-433 187 0\n-434 242 0\n-434 73 74 75 76 80 81 82 83 0\n-434 74 75 76 81 82 83 88 89 90 0\n-434 74 76 81 83 88 90 103 104 0\n-434 76 83 90 97 104 0\n-435 298 0\n-435 127 128 129 131 156 157 158 159 0\n436 437 438 0\n-436 188 0\n-437 243 0\n-437 80 82 83 77 95 96 97 91 0\n-438 299 0\n-438 136 137 138 132 143 144 145 139 0\n-438 137 138 132 144 145 139 151 152 146 0\n-438 138 132 145 139 152 146 159 153 0\n439 440 441 0\n-439 195 0\n-439 34 28 29 41 35 36 48 42 43 0\n-440 251 0\n-440 85 92 99 106 56 0\n-441 307 0\n-441 143 144 145 139 140 0\n-441 143 144 145 140 116 117 118 112 0\n-441 143 145 140 158 159 154 116 118 112 0\n442 443 444 0\n-442 40 41 35 36 37 0\n-442 40 35 36 37 55 49 50 51 0\n-443 259 0\n-443 92 93 99 100 106 107 56 57 0\n-444 315 0\n445 446 447 0\n-445 48 42 43 45 20 14 15 16 0\n-445 45 52 2 9 16 0\n-446 267 0\n-446 104 98 99 100 101 0\n-447 323 0\n448 449 450 0\n-448 219 0\n-448 49 50 53 14 15 17 21 22 24 0\n-448 49 53 7 10 14 17 21 24 0\n-449 275 0\n-449 105 106 107 109 77 78 79 80 0\n-449 106 107 109 56 57 59 78 79 80 0\n-449 105 107 109 63 64 66 77 79 80 0\n-449 105 106 109 70 71 73 77 78 80 0\n-449 109 59 66 73 80 0\n-450 331 0\n-450 161 162 163 164 112 113 114 115 0\n-450 162 163 164 113 114 115 120 121 122 0\n-450 163 164 114 115 121 122 127 128 0\n451 452 453 0\n-451 172 0\n-451 3 4 5 10 11 12 17 18 19 24 25 26 0\n-451 3 5 10 12 17 19 24 26 39 40 0\n-451 2 5 9 12 16 19 31 33 38 40 0\n-451 5 12 19 26 33 40 0\n-452 227 0\n-452 56 57 58 59 60 61 0\n-452 56 57 59 60 61 78 79 80 81 82 0\n-452 56 57 60 61 78 79 81 82 85 86 88 89 0\n-453 283 0\n454 455 456 0\n-454 180 0\n-455 235 0\n-455 64 65 66 67 68 69 0\n-455 64 66 67 68 69 79 80 81 82 83 0\n-455 64 65 67 68 69 86 87 88 89 90 0\n-455 64 67 68 69 79 81 82 83 86 88 89 90 0\n-455 64 65 66 68 69 93 94 95 96 97 0\n-455 64 66 68 69 79 80 82 83 93 95 96 97 0\n-455 64 68 69 79 82 83 86 89 90 93 96 97 0\n-455 68 69 75 76 82 83 89 90 96 97 0\n-455 64 66 67 69 79 80 81 83 100 102 103 104 0\n-455 64 65 69 86 87 90 93 94 97 100 101 104 0\n-455 64 69 79 83 86 90 93 97 100 104 0\n-455 69 76 83 90 97 104 0\n-456 291 0\n-456 120 121 122 123 124 125 0\n-456 120 121 123 124 125 141 142 143 144 145 0\n-456 120 123 124 125 134 136 137 138 141 143 144 145 0\n-456 120 121 122 124 125 148 149 150 151 152 0\n-456 120 121 122 125 148 149 150 152 155 156 157 159 0\n457 458 459 0\n-457 189 0\n-458 244 0\n-459 136 137 138 132 133 143 144 145 139 140 0\n-459 136 138 132 133 143 145 139 140 158 159 153 154 0\n-459 136 137 138 133 143 144 145 140 116 117 118 112 0\n-459 137 138 133 144 145 140 151 152 147 117 118 112 0\n-459 136 138 133 143 145 140 158 159 154 116 118 112 0\n-459 138 133 145 140 152 147 159 154 118 112 0\n-459 136 133 143 140 158 154 165 161 116 112 0\n-459 133 140 147 154 161 112 0\n460 461 462 0\n-460 32 33 34 28 29 30 0\n-460 33 34 28 29 30 40 41 35 36 37 0\n-460 32 34 28 29 30 47 48 42 43 44 0\n-460 34 28 29 30 41 35 36 37 48 42 43 44 0\n-460 32 33 28 29 30 54 55 49 50 51 0\n-460 33 28 29 30 40 35 36 37 55 49 50 51 0\n-461 252 0\n-462 308 0\n463 464 465 0\n-463 204 0\n-463 40 41 35 36 37 38 0\n-463 40 41 35 36 38 19 20 14 15 16 0\n-463 35 36 38 42 43 45 49 50 52 14 15 16 0\n-463 40 41 35 38 12 13 7 9 19 20 14 16 0\n-463 41 35 38 48 42 45 13 7 9 20 14 16 0\n-463 40 35 38 55 49 52 12 7 9 19 14 16 0\n-463 35 38 42 45 49 52 7 9 14 16 0\n-463 40 41 38 5 6 2 12 13 9 19 20 16 0\n-463 40 38 55 52 5 2 12 9 19 16 0\n-464 260 0\n-464 96 97 91 92 93 94 0\n-464 97 91 92 93 94 104 98 99 100 101 0\n-464 96 91 92 93 94 111 105 106 107 108 0\n-464 96 97 92 93 94 61 62 56 57 58 0\n-464 92 93 94 99 100 101 106 107 108 56 57 58 0\n-464 93 94 100 101 107 108 57 58 64 65 0\n-465 316 0\n466 467 468 0\n-466 212 0\n-466 48 42 46 13 7 10 20 14 17 27 21 24 0\n-466 42 46 49 53 7 10 14 17 21 24 0\n-467 268 0\n-467 104 98 99 100 101 102 0\n-467 104 98 99 100 102 83 77 78 79 80 0\n-468 324 0\n-468 159 155 156 157 118 113 114 115 125 120 121 122 0\n469 470 471 0\n-469 220 0\n-469 49 50 51 53 54 21 22 23 24 25 0\n-469 49 50 53 54 14 15 17 18 21 22 24 25 0\n-470 276 0\n-470 105 106 107 108 109 110 0\n-470 105 106 107 108 110 84 85 86 87 88 0\n-470 110 60 67 74 81 88 0\n-471 332 0\n-471 160 162 163 164 165 119 120 121 122 123 0\n-471 162 163 164 165 113 114 115 116 120 121 122 123 0\n-471 162 163 165 113 114 116 120 121 123 141 142 143 0\n-471 161 163 165 112 114 116 126 127 129 140 142 143 0\n-471 163 165 114 116 121 123 127 129 142 143 0\n-471 165 116 123 129 136 143 0\n"
 "1205 -6 0 645 145 0\n1206 -62 0 646 310 0\n1207 -118 0 647 493 0\n1208 -7 0 648 146 0\n1209 -63 0 649 311 0\n1210 -119 0 650 494 0\n1211 -15 0 651 154 0\n1212 -71 0 652 317 0\n1213 -126 0 653 500 0\n1214 -23 0 654 161 0\n1215 -79 0 655 325 0\n1216 -134 0 656 506 0\n1217 -31 0 657 167 0\n1218 -87 0 658 332 0\n1219 -142 0 659 514 0\n1220 -39 0 661 175 0\n1221 -95 0 662 340 0\n1222 -150 0 663 521 0\n1223 -47 0 665 183 0\n1224 -103 0 666 348 0\n1225 -158 0 667 529 0\n1226 -55 0 669 190 0\n1227 -111 0 670 356 0\n1228 -166 0 671 537 0\n1229 -56 0 673 1 0\n1230 -112 0 673 2 0\n1231 167 0 673 140 0\n1232 -180 0 1231 645 195 0\n1233 -181 0 1231 651 222 0\n1234 -13 0 1232 152 0\n1235 -14 0 1233 153 0\n1236 -64 0 674 35 0\n1237 -120 0 674 36 0\n1238 175 0 674 147 0\n1239 168 0 1238 1231 191 0\n1240 -187 0 1238 1232 209 0\n1241 -189 0 1238 654 235 0\n1242 -188 0 1239 654 234 0\n1243 -20 0 1240 158 0\n1244 -22 0 1241 160 0\n1245 -21 0 1242 159 0\n1246 -16 0 675 73 0\n1247 -127 0 675 74 0\n1248 238 0 675 318 0\n1249 -244 0 1248 652 388 0\n1250 -252 0 1248 658 419 0\n1251 -78 0 1249 324 0\n1252 -86 0 1250 331 0\n1253 -24 0 676 90 0\n1254 -80 0 676 91 0\n1255 302 0 676 507 0\n1256 -308 0 1255 656 586 0\n1257 -316 0 1255 663 613 0\n1258 -141 0 1256 513 0\n1259 -149 0 1257 520 0\n1260 -65 -132 0 673 677 0\n1261 -121 -77 0 673 678 0\n1262 -66 -139 0 673 679 0\n1263 -122 -84 0 673 680 0\n1264 -67 -146 0 673 681 0\n1265 -123 -91 0 673 682 0\n1266 -68 -153 0 673 683 0\n1267 -124 -98 0 673 684 0\n1268 -69 -160 0 673 685 0\n1269 -125 -105 0 673 686 0\n1270 -2 -84 0 676 687 0\n1271 -58 -28 0 676 688 0\n1272 -133 0 674 675 721 0\n1273 -73 -140 0 674 722 0\n1274 -74 -147 0 674 723 0\n1275 -129 -92 0 674 724 0\n1276 -75 -154 0 674 725 0\n1277 -76 -161 0 674 726 0\n1278 -131 -106 0 674 727 0\n1279 -9 -85 0 676 728 0\n1280 -65 -29 0 676 729 0\n1281 -30 0 675 676 755 0\n1282 -136 -37 0 675 756 0\n1283 -138 -51 0 675 757 0\n1284 -32 -94 0 676 767 0\n1285 -88 -38 0 676 768 0\n1286 -33 -101 0 676 769 0\n1287 -89 -45 0 676 770 0\n1288 -34 -108 0 676 771 0\n1289 -90 -52 0 676 772 0\n1290 334 0 673 676 789 0\n1291 -143 335 0 1290 674 790 0\n1292 -335 -40 336 0 675 791 0\n1293 -335 -151 0 675 792 0\n1294 -336 -48 0 676 793 0\n1295 -336 -104 337 0 676 794 0\n1296 -336 -159 0 676 795 0\n1297 338 0 673 676 798 0\n1298 -143 339 0 1297 674 799 0\n1299 -339 -96 340 0 675 800 0\n1300 -340 -48 341 0 676 801 0\n1301 -340 -104 0 676 802 0\n1302 -340 -159 0 676 803 0\n1303 -88 342 0 673 806 0\n1304 -342 -96 343 0 674 807 0\n1305 -343 -104 0 675 808 0\n1306 -88 344 0 673 809 0\n1307 -344 -96 345 0 674 810 0\n1308 -345 -104 0 675 811 0\n1309 -345 -159 346 0 675 812 0\n1310 -346 -105 0 676 813 0\n1311 -40 347 0 673 814 0\n1312 -347 -48 348 0 674 815 0\n1313 -348 -105 349 0 675 816 0\n1314 -349 0 676 673 817 0\n1315 -40 350 0 673 818 0\n1316 -350 -48 351 0 674 819 0\n1317 -351 -160 352 0 675 820 0\n1318 -352 0 676 673 821 0\n1319 -104 353 0 673 822 0\n1320 -353 -105 354 0 674 823 0\n1321 -354 355 0 675 673 824 0\n1322 -355 0 676 674 825 0\n1323 -354 0 1322 1321 0\n1324 -159 356 0 673 826 0\n1325 -356 -160 357 0 674 827 0\n1326 -357 358 0 675 673 828 0\n1327 -358 0 676 674 829 0\n1328 -357 0 1327 1326 0\n1329 -49 359 0 673 830 0\n1330 -359 360 0 674 673 831 0\n1331 -360 0 675 674 832 0\n1332 -359 0 1331 1330 0\n1333 -49 0 1332 1329 0\n1334 235 291 0 1232 841 0\n1335 242 298 0 1240 845 0\n1336 236 292 0 1233 846 0\n1337 243 299 0 1242 849 0\n1338 300 0 1241 1249 850 0\n1339 -294 0 1338 653 571 0\n1340 -286 0 1338 656 582 0\n1341 196 0 1250 1256 855 0\n1342 -183 0 1341 657 248 0\n1343 204 260 0 1257 860 0\n1344 -361 9 0 1246 870 0\n1345 -365 81 0 1254 876 0\n1346 -373 42 0 1333 896 0\n1347 -376 50 0 1333 905 0\n1348 -377 106 0 1229 907 0\n1349 -378 161 0 1230 909 0\n1350 -379 2 9 0 1246 912 0\n1351 -380 57 58 0 1229 914 0\n1352 -381 114 0 1230 1213 1247 916 0\n1353 -382 10 17 0 1253 919 0\n1354 -383 66 0 1236 1215 1254 920 0\n1355 -384 121 122 0 1237 922 0\n1356 -385 17 18 0 1246 925 0\n1357 -386 73 74 81 0 1254 927 0\n1358 -387 129 143 0 1247 1219 930 0\n1359 -389 81 82 0 1254 934 0\n1360 -391 32 34 48 0 1223 940 0\n1361 -392 88 90 104 0 1224 945 0\n1362 -393 143 145 159 0 1225 948 0\n1363 -394 40 35 0 1226 1333 951 0\n1364 -394 35 42 0 1333 952 0\n1365 -395 96 91 105 0 1227 955 0\n1366 -398 99 106 0 1229 964 0\n1367 -399 159 154 0 1207 1230 965 0\n1368 -400 50 51 0 1333 968 0\n1369 -401 105 107 0 1209 1236 970 0\n1370 -401 107 57 0 1236 971 0\n1371 -404 57 59 0 1229 1251 1215 1254 975 0\n1372 -406 10 11 17 18 25 0 1253 979 0\n1373 -407 66 67 81 0 1236 1215 1254 981 0\n1374 -407 67 81 88 0 1236 1215 1252 982 0\n1375 -408 121 122 123 0 1237 984 0\n1376 -408 121 123 143 0 1237 1258 1219 985 0\n1377 -410 73 74 75 81 82 0 1254 989 0\n1378 -411 129 130 143 144 0 1247 1219 992 0\n1379 -412 26 27 40 41 0 1253 1220 995 0\n1380 -412 25 27 46 48 0 1253 1223 996 0\n1381 -412 27 41 46 48 0 1253 1220 997 0\n1382 -413 82 83 96 97 0 1254 1221 999 0\n1383 -415 32 34 28 48 42 0 1223 1004 0\n1384 -415 32 33 28 54 0 1226 1333 1005 0\n1385 -415 32 28 42 54 0 1223 1333 1006 0\n1386 -415 28 35 42 0 1333 1007 0\n1387 -416 88 90 84 104 98 0 1224 1011 0\n1388 -416 88 89 84 110 105 0 1227 1013 0\n1389 -416 89 84 96 91 105 0 1227 1014 0\n1390 -416 88 84 98 110 105 0 1224 1015 0\n1391 -417 143 145 139 159 153 0 1225 1019 0\n1392 -417 143 139 153 165 160 0 1225 1020 0\n1393 -420 151 152 147 117 0 1207 1230 1026 0\n1394 -420 152 147 159 154 0 1207 1230 1027 0\n1395 -422 98 100 105 107 0 1209 1236 1031 0\n1396 -424 50 52 0 1333 1235 1211 1246 1035 0\n1397 -425 106 107 108 57 58 0 1229 1038 0\n1398 -425 105 107 108 65 0 1209 1236 1039 0\n1399 -426 163 114 121 0 1247 1041 0\n1400 -427 3 4 10 11 17 18 25 0 1253 1044 0\n1401 -428 60 74 81 85 88 0 1229 1212 1251 1047 0\n1402 -429 113 114 116 140 143 0 1230 1258 1219 1049 0\n1403 -431 66 67 68 81 82 0 1236 1215 1254 1053 0\n1404 -432 121 122 123 124 0 1237 1056 0\n1405 -432 121 123 124 143 144 0 1237 1258 1219 1057 0\n1406 -433 0 1240 1059 0\n1407 -434 73 74 75 76 81 82 83 0 1254 1061 0\n1408 -434 74 76 81 83 88 90 104 0 1224 1063 0\n1409 -435 128 129 131 156 157 159 0 1247 1225 1066 0\n1410 -436 0 1242 1068 0\n1411 -437 82 83 77 96 97 91 0 1254 1221 1070 0\n1412 -440 85 92 99 106 0 1229 1079 0\n1413 -441 143 144 145 140 116 117 0 1207 1230 1082 0\n1414 -441 143 145 140 159 154 116 0 1225 1207 1230 1083 0\n1415 -442 40 35 36 37 50 51 0 1226 1333 1086 0\n1416 -443 92 93 99 100 106 107 57 0 1229 1088 0\n1417 -445 48 42 43 45 0 1243 1235 1211 1246 1091 0\n1418 -445 45 52 2 9 0 1246 1092 0\n1419 -448 50 53 17 0 1333 1235 1211 1245 1244 1253 1098 0\n1420 -448 53 10 17 0 1333 1208 1235 1245 1253 1099 0\n1421 -449 105 106 107 109 77 0 1251 1215 1254 1101 0\n1422 -449 106 107 109 57 59 0 1229 1251 1215 1254 1102 0\n1423 -449 105 107 109 66 77 0 1209 1236 1215 1254 1103 0\n1424 -449 105 106 109 70 73 77 0 1212 1251 1254 1104 0\n1425 -449 109 59 66 73 0 1254 1105 0\n1426 -450 161 162 163 164 113 114 115 0 1230 1107 0\n1427 -450 162 163 164 113 114 115 121 122 0 1237 1108 0\n1428 -450 163 164 114 115 121 122 128 0 1247 1109 0\n1429 -451 3 4 5 10 11 12 17 18 19 25 26 0 1253 1112 0\n1430 -451 3 5 10 12 17 19 26 40 0 1253 1220 1113 0\n1431 -451 2 5 9 12 19 33 38 40 0 1246 1217 1114 0\n1432 -452 57 58 59 60 61 0 1229 1117 0\n1433 -452 57 59 60 61 81 82 0 1229 1251 1215 1254 1118 0\n1434 -452 57 60 61 81 82 85 88 89 0 1229 1251 1215 1252 1119 0\n1435 -454 0 1232 1122 0\n1436 -455 65 66 67 68 69 0 1236 1124 0\n1437 -455 66 67 68 69 81 82 83 0 1236 1215 1254 1125 0\n1438 -455 65 67 68 69 88 89 90 0 1236 1252 1218 1126 0\n1439 -455 67 68 69 81 82 83 88 89 90 0 1236 1215 1252 1127 0\n1440 -455 65 66 68 69 93 94 96 97 0 1236 1221 1128 0\n1441 -455 66 68 69 82 83 93 96 97 0 1236 1215 1254 1221 1129 0\n1442 -455 68 69 82 83 89 90 93 96 97 0 1236 1215 1252 1130 0\n1443 -455 66 67 69 81 83 100 102 104 0 1236 1215 1254 1224 1132 0\n1444 -455 65 69 90 93 94 97 100 101 104 0 1236 1252 1218 1133 0\n1445 -455 69 83 90 93 97 100 104 0 1236 1215 1252 1134 0\n1446 -456 121 122 123 124 125 0 1237 1137 0\n1447 -456 121 123 124 125 143 144 145 0 1237 1258 1219 1138 0\n1448 -456 123 124 125 136 137 138 143 144 145 0 1237 1216 1258 1139 0\n1449 -456 121 122 124 125 148 151 152 0 1237 1259 1222 1140 0\n1450 -456 121 122 125 148 152 155 156 157 159 0 1237 1259 1222 1141 0\n1451 -457 0 1241 1143 0\n1452 -458 0 1249 1144 0\n1453 459 0 1452 1451 1142 0\n1454 136 137 138 132 143 144 145 139 140 0 1453 1272 1145 0\n1455 136 138 132 143 145 139 140 159 153 154 0 1453 1272 1225 1146 0\n1456 136 137 138 143 144 145 140 116 117 0 1453 1272 1207 1230 1147 0\n1457 137 138 144 145 140 151 152 147 117 0 1453 1272 1207 1230 1148 0\n1458 136 138 143 145 140 159 154 116 0 1453 1272 1225 1207 1230 1149 0\n1459 138 145 140 152 147 159 154 0 1453 1272 1207 1230 1150 0\n1460 136 143 140 154 165 161 116 0 1453 1272 1225 1230 1151 0\n1461 140 147 154 161 0 1453 1272 1230 1152 0\n1462 -460 32 33 34 28 29 0 1281 1154 0\n1463 -460 33 34 28 29 40 41 35 36 37 0 1281 1155 0\n1464 -460 32 34 28 29 48 42 43 44 0 1281 1223 1156 0\n1465 -460 34 28 29 41 35 36 37 48 42 43 44 0 1281 1157 0\n1466 -460 32 33 28 29 54 50 51 0 1281 1226 1333 1158 0\n1467 -460 33 28 29 40 35 36 37 50 51 0 1281 1226 1333 1159 0\n1468 -461 0 1250 1160 0\n1469 -462 0 1256 1161 0\n1470 460 0 1469 1468 1153 0\n1471 -463 40 41 35 36 38 19 0 1243 1235 1211 1246 1165 0\n1472 -463 35 36 38 42 43 45 50 52 0 1333 1235 1211 1246 1166 0\n1473 -463 40 41 35 38 12 9 19 0 1234 1208 1243 1235 1246 1167 0\n1474 -463 41 35 38 48 42 45 9 0 1234 1208 1243 1235 1246 1168 0\n1475 -463 40 35 38 52 12 9 19 0 1226 1333 1208 1235 1246 1169 0\n1476 -463 35 38 42 45 52 9 0 1333 1208 1235 1246 1170 0\n1477 -463 40 41 38 5 2 12 9 19 0 1205 1234 1243 1246 1171 0\n1478 -463 40 38 52 5 2 12 9 19 0 1226 1246 1172 0\n1479 -464 96 91 92 93 94 105 106 107 108 0 1227 1176 0\n1480 -464 96 97 92 93 94 61 57 58 0 1206 1229 1177 0\n1481 -464 92 93 94 99 100 101 106 107 108 57 58 0 1229 1178 0\n1482 -464 93 94 100 101 107 108 57 58 65 0 1236 1179 0\n1483 -465 0 1257 1180 0\n1484 -466 48 42 46 10 17 27 0 1234 1208 1243 1235 1245 1253 1183 0\n1485 -466 42 46 53 10 17 0 1333 1208 1235 1245 1253 1184 0\n1486 -467 104 98 99 100 102 83 77 0 1251 1215 1254 1187 0\n1487 -468 159 155 156 157 113 114 115 125 121 122 0 1207 1237 1189 0\n1488 -469 50 51 53 54 25 0 1333 1245 1244 1214 1253 1192 0\n1489 -469 50 53 54 17 18 25 0 1333 1235 1211 1245 1244 1253 1193 0\n1490 -470 105 106 107 108 110 84 85 88 0 1252 1218 1196 0\n1491 -471 160 162 163 164 165 121 122 123 0 1210 1237 1199 0\n1492 -471 162 163 164 165 113 114 115 116 121 122 123 0 1237 1200 0\n1493 -471 162 163 165 113 114 116 121 123 143 0 1237 1258 1219 1201 0\n1494 -471 161 163 165 114 116 129 140 143 0 1230 1213 1247 1219 1202 0\n1495 -471 163 165 114 116 121 123 129 143 0 1247 1219 1203 0\n1496 -160 104 97 90 83 76 0 650 1435 531 1268 567 1135 1136 1121 0\n1497 89 233 234 88 -455 69 90 83 0 314 315 1438 312 372 373 326 327 1439 0\n1498 -204 206 199 19 -451 5 34 28 0 657 1470 176 169 251 266 168 163 1462 1115 166 151 247 0\n1499 -151 140 304 145 138 139 132 0 1255 587 515 509 522 1293 590 1291 508 1454 0\n1500 -143 -48 -105 0 1314 1313 1312 1311 1291 1298 804 1293 1300 664 1299 0\n1501 -48 60 -160 59 58 57 0 671 645 531 634 1120 184 720 205 1432 1111 1110 0\n1502 -96 234 345 -455 90 83 69 0 315 341 1307 380 1306 314 1497 334 376 313 1436 312 372 373 326 327 1437 0\n1503 233 66 234 -455 83 69 0 315 314 1436 312 372 373 326 327 1437 0\n1504 -89 234 152 -455 159 83 69 -3 -2 0 661 649 315 142 260 950 334 702 376 313 1503 377 953 949 959 1264 689 1436 1437 312 327 373 0\n1505 233 -254 234 -455 83 69 0 1503 375 313 0\n1506 88 233 89 82 68 -455 90 83 69 0 314 1438 1439 312 326 372 0\n1507 -116 -98 96 283 0 1225 1224 1223 491 713 549 124 522 0\n1508 288 123 124 -105 0 649 1435 1255 350 383 1123 1121 1269 496 554 1446 495 0\n1509 -143 340 336 0 1291 1298 1292 1293 1299 664 0\n1510 -160 -337 32 0 1222 1221 1220 796 797 106 0\n1511 206 36 41 -88 35 0 658 1483 333 421 1173 1162 1285 176 1471 1164 157 173 265 0\n1512 -225 60 4 116 82 68 88 35 227 -160 -2 0 650 1435 646 662 531 567 1136 1121 696 1268 363 432 362 335 336 334 19 1264 689 1439 0\n1513 90 89 60 4 116 82 68 88 35 -160 -2 0 650 1435 649 531 567 1136 1121 696 1268 1506 377 336 19 1264 689 1439 0\n1514 66 4 82 60 234 116 35 -160 -2 0 650 1435 649 315 531 567 1136 1121 696 1268 1503 377 336 19 1264 689 1437 0\n1515 4 82 60 234 116 153 143 88 35 -160 -2 0 657 1328 649 315 1325 1324 141 245 1003 1514 313 1262 374 376 1008 334 1002 1513 1391 121 0\n1516 82 370 -98 153 96 143 88 394 35 -104 -160 -2 113 0 645 671 649 666 1225 1224 1223 1410 669 1257 650 656 343 453 308 381 531 634 1507 349 469 1194 696 34 141 197 994 7 6 1515 21 715 711 1365 890 1411 1382 124 949 886 1067 993 176 785 957 892 1071 1000 304 562 619 553 594 1191 497 534 495 533 1190 1493 0\n1517 -98 -96 143 345 -455 159 83 69 415 0 649 341 31 343 381 1502 380 121 1503 313 1262 374 1391 1008 1002 0\n1518 233 66 82 68 -455 83 69 0 314 1437 1436 326 312 372 0\n1519 82 115 116 4 68 60 88 35 227 -160 3 -2 0 657 650 1435 649 531 567 1136 1121 696 1268 141 245 165 1270 1512 307 10 1262 1518 377 336 19 1264 689 1437 0\n1520 -88 40 212 343 0 666 1225 1224 1223 663 333 1303 463 1304 863 124 618 522 0\n1521 -124 104 373 0 650 498 1267 566 898 900 894 0\n1522 98 -395 288 -105 373 0 649 1435 1255 650 1323 1340 1320 1319 1521 1508 497 563 519 562 1265 554 495 496 350 383 1123 1121 1269 898 954 894 133 900 1449 614 522 0\n1523 -320 35 148 313 91 121 122 60 124 -105 0 649 1435 667 517 350 383 1123 1121 1269 621 614 491 522 19 1449 716 0\n1524 -152 35 146 91 60 -105 0 647 523 716 550 19 491 0\n1525 201 -306 60 -105 373 0 649 1435 1255 1340 1323 650 1338 667 647 558 1320 1319 1521 1508 497 583 626 527 563 519 562 957 517 1265 554 495 496 350 383 1123 1121 1269 171 950 949 1522 1523 628 528 1524 1449 127 522 711 616 19 526 1507 1450 552 530 0\n1526 -143 -105 0 1323 1320 1319 1500 668 1296 1302 1509 0\n1527 104 48 153 98 373 0 1328 898 668 894 1324 902 1325 0\n1528 -283 -347 0 647 671 1333 1207 1206 1205 1314 1323 1228 1227 1226 552 634 530 531 33 1313 1320 1312 1319 136 0\n1529 -40 451 0 646 670 1333 1207 1206 1205 1318 1328 1228 1227 1226 1311 1315 1528 1120 1110 1116 368 471 349 350 33 1317 1325 1316 1324 136 0\n1530 -143 -227 0 670 1205 1206 1207 1333 1328 646 368 349 471 350 33 1325 1324 668 1294 805 1509 1300 0\n1531 -153 -311 394 -105 0 1323 650 1320 1319 30 31 524 1346 566 1521 560 1522 1508 949 497 957 562 0\n1532 -140 123 124 -105 0 649 1435 659 350 383 1123 1121 1269 49 512 1446 598 495 0\n1533 -328 331 124 332 -105 0 636 637 1508 497 0\n1534 201 416 42 139 28 -311 165 -105 0 1526 34 171 950 1386 1531 1002 1392 0\n1535 -208 -206 -451 5 0 661 648 1233 1242 1231 1239 665 267 220 232 240 271 272 275 274 151 218 157 231 163 239 278 280 143 142 150 156 162 149 155 1429 0\n1536 -184 42 212 48 0 1239 1238 1233 651 1240 661 1470 196 206 223 224 227 264 280 260 262 278 165 166 170 173 180 171 172 179 1465 1464 177 168 253 0\n1537 -10 178 179 34 0 648 1470 42 149 212 214 213 169 168 1462 165 0\n1538 -140 17 0 653 1258 1252 1281 512 1273 572 75 501 0\n1539 -147 124 -105 0 663 58 518 1508 610 0\n1540 -140 42 48 -105 0 1323 1340 661 665 1250 1222 1221 1220 1320 1319 1346 1521 1526 1532 1538 497 155 563 264 1536 859 284 420 168 333 106 0\n1541 -451 -42 -105 0 649 647 1338 648 1233 1242 657 658 645 178 240 163 232 157 220 151 29 350 383 1334 538 540 1526 1535 176 1115 112 169 255 226 214 273 155 149 833 1430 413 142 707 427 200 947 942 938 937 0\n1542 -32 106 34 59 -152 220 145 57 0 663 1250 523 620 1106 535 168 301 188 1097 780 1096 116 335 428 352 1422 0\n1543 -328 121 332 145 124 -105 0 649 1435 671 350 383 1123 1121 1526 1269 1533 637 642 497 515 1447 0\n1544 58 77 2 114 132 0 1245 4 0\n1545 160 105 0 1205 1206 1207 1333 33 0\n1546 65 9 121 0 1244 1251 1272 37 0\n1547 50 161 69 125 106 0 1234 66 0\n1548 17 73 128 0 1281 1252 1258 75 0\n1549 107 76 131 51 162 0 1243 88 0\n1550 81 136 25 38 94 0 1259 92 0\n1551 88 32 143 0 1220 1221 1222 106 0\n1552 40 151 96 0 1223 1224 1225 124 0\n1553 48 159 104 0 1226 1227 1228 136 0\n1554 -176 169 0 1231 192 0\n1555 -177 170 0 1231 193 0\n1556 -178 171 0 1231 194 0\n1557 -184 170 0 1239 196 0\n1558 -169 -193 0 645 197 0\n1559 -170 -200 0 645 200 0\n1560 -171 -207 0 645 202 0\n1561 -172 -214 0 645 205 0\n1562 -184 177 0 1238 206 0\n1563 -185 178 0 1238 207 0\n1564 -186 179 0 1238 208 0\n1565 -176 -193 0 1232 211 0\n1566 -177 -194 0 648 212 0\n1567 -177 -200 0 1232 215 0\n1568 -178 -201 0 648 216 0\n1569 -178 -207 0 1232 219 0\n1570 -179 -208 0 648 220 0\n1571 -179 -214 0 1232 221 0\n1572 -184 -194 0 1233 223 0\n1573 -184 -195 0 651 224 0\n1574 -184 -200 0 1240 227 0\n1575 -185 -201 0 1233 228 0\n1576 -185 -202 0 651 229 0\n1577 -185 -204 0 1342 230 0\n1578 -186 -208 0 1233 232 0\n1579 -186 -214 0 1240 233 0\n1580 -191 -201 0 1242 236 0\n1581 -191 -202 0 1241 237 0\n1582 -191 -203 0 654 238 0\n1583 -192 -208 0 1242 240 0\n1584 -192 -209 0 1241 241 0\n1585 -193 -216 0 1241 243 0\n1586 -194 195 0 1231 244 0\n1587 -194 -169 0 657 245 0\n1588 -195 -176 0 657 246 0\n1589 -198 -204 0 657 251 0\n1590 -199 -211 0 657 255 0\n1591 -200 -218 0 657 256 0\n1592 -201 202 0 1231 258 0\n1593 -201 -170 0 661 260 0\n1594 -202 -177 0 661 262 0\n1595 -203 -184 0 661 264 0\n1596 -206 -212 0 661 267 0\n1597 -207 -219 0 661 270 0\n1598 -208 209 0 1231 271 0\n1599 -208 -171 0 665 275 0\n1600 -209 210 0 1238 276 0\n1601 -209 -178 0 665 279 0\n1602 -210 -185 0 665 281 0\n1603 -211 -191 0 665 282 0\n1604 -212 -198 0 665 284 0\n1605 -214 -220 0 665 287 0\n1606 -215 -172 0 669 289 0\n1607 -216 217 0 1238 290 0\n1608 -216 -179 0 669 294 0\n1609 -217 -186 0 669 296 0\n1610 -218 -192 0 669 298 0\n1611 -219 217 0 1341 300 0\n1612 -219 -199 0 669 302 0\n1613 -220 -206 0 669 304 0\n1614 -222 -235 0 646 357 0\n1615 -223 224 0 1248 358 0\n1616 -223 -242 0 646 359 0\n1617 -224 -249 0 646 361 0\n1618 -225 -256 0 646 363 0\n1619 -226 -263 0 646 366 0\n1620 -227 -270 0 646 368 0\n1621 -230 -236 0 649 369 0\n1622 -230 231 0 1248 370 0\n1623 -231 -243 0 649 371 0\n1624 -232 -250 0 649 374 0\n1625 -233 -257 0 649 377 0\n1626 -234 -264 0 649 381 0\n1627 -235 -271 0 649 383 0\n1628 -243 236 0 1248 387 0\n1629 -247 240 0 1248 389 0\n1630 -240 -258 0 652 393 0\n1631 -241 -265 0 652 395 0\n1632 -242 -272 0 652 396 0\n1633 -243 -223 0 655 397 0\n1634 -247 -258 0 1249 400 0\n1635 -247 -259 0 655 401 0\n1636 -248 -265 0 1249 405 0\n1637 -248 -266 0 655 406 0\n1638 -249 -272 0 1249 409 0\n1639 -249 -273 0 655 410 0\n1640 -250 -223 0 1250 412 0\n1641 -250 -224 0 658 413 0\n1642 -251 -230 0 1250 415 0\n1643 -251 -231 0 658 416 0\n1644 -254 -259 0 1250 420 0\n1645 -254 -260 0 658 421 0\n1646 -255 -266 0 1250 424 0\n1647 -255 -267 0 658 425 0\n1648 -256 -273 0 1250 428 0\n1649 -256 -274 0 658 429 0\n1650 -257 -225 0 662 432 0\n1651 -259 -239 0 662 436 0\n1652 -260 -246 0 662 439 0\n1653 -262 -268 0 662 444 0\n1654 -263 -275 0 662 449 0\n1655 -264 -226 0 666 453 0\n1656 -265 -233 0 666 456 0\n1657 -266 -240 0 666 458 0\n1658 -267 -247 0 666 460 0\n1659 -268 -254 0 666 463 0\n1660 -270 -276 0 666 469 0\n1661 -271 -227 0 670 471 0\n1662 -272 -234 0 670 474 0\n1663 -273 274 0 1248 476 0\n1664 -273 -241 0 670 479 0\n1665 -274 -248 0 670 482 0\n1666 -275 -255 0 670 485 0\n1667 -276 -262 0 670 487 0\n1668 -278 -291 0 647 538 0\n1669 -279 -298 0 647 539 0\n1670 -280 278 0 1338 540 0\n1671 -280 281 0 1255 541 0\n1672 -280 -305 0 647 544 0\n1673 -281 -312 0 647 547 0\n1674 -282 -319 0 647 550 0\n1675 -283 -326 0 647 552 0\n1676 -287 -299 0 650 553 0\n1677 -287 288 0 1255 554 0\n1678 -288 -306 0 650 558 0\n1679 -289 -313 0 650 562 0\n1680 -290 -320 0 650 566 0\n1681 -291 -327 0 650 567 0\n1682 -292 -278 0 653 570 0\n1683 -295 -307 0 653 572 0\n1684 -296 -314 0 653 575 0\n1685 -297 -321 0 653 578 0\n1686 -298 -328 0 653 579 0\n1687 -298 -330 0 1339 580 0\n1688 -299 -279 0 656 581 0\n1689 -289 303 0 1338 583 0\n1690 -290 304 0 1338 584 0\n1691 -306 299 0 1255 585 0\n1692 -311 304 0 1255 587 0\n1693 -312 305 0 1255 588 0\n1694 -303 -315 0 656 589 0\n1695 -305 -329 0 656 594 0\n1696 -306 -279 0 1256 595 0\n1697 -306 -280 0 659 596 0\n1698 -307 -287 0 659 598 0\n1699 -311 -322 0 1256 601 0\n1700 -311 -323 0 659 602 0\n1701 -312 -329 0 1256 604 0\n1702 -312 -330 0 659 605 0\n1703 -313 -280 0 1257 607 0\n1704 -313 -281 0 663 608 0\n1705 -314 -287 0 1257 609 0\n1706 -314 -288 0 663 610 0\n1707 -318 -323 0 1257 617 0\n1708 -318 -324 0 663 618 0\n1709 -319 -330 0 1257 619 0\n1710 -319 -331 0 663 620 0\n1711 -320 -282 0 667 621 0\n1712 -321 -289 0 667 624 0\n1713 -322 -296 0 667 625 0\n1714 -323 -303 0 667 626 0\n1715 -324 -310 0 667 629 0\n1716 -326 -332 0 667 631 0\n1717 -327 -283 0 671 634 0\n1718 -328 -290 0 671 638 0\n1719 -330 328 0 1338 639 0\n1720 -330 331 0 1255 640 0\n1721 -330 -304 0 671 641 0\n1722 -331 -311 0 671 642 0\n1723 -332 -318 0 671 644 0\n1724 105 160 0 1333 672 0\n1725 -351 -160 0 1318 1317 0\n1726 -353 -105 0 1323 1320 0\n1727 -356 -160 0 1328 1325 0\n1728 434 435 0 1406 1058 0\n1729 437 438 0 1410 1067 0\n1730 455 456 0 1435 1121 0\n1731 32 33 29 34 28 0 1470 1462 0\n1732 37 41 29 36 35 40 28 34 33 0 1470 1463 0\n1733 44 32 43 34 48 28 42 29 0 1470 1464 0\n1734 44 37 43 36 35 41 34 48 42 29 28 0 1470 1465 0\n1735 32 33 51 50 28 29 54 0 1470 1466 0\n1736 37 50 51 28 40 33 29 36 35 0 1470 1467 0\n1737 463 464 0 1483 1162 0\n1738 -28 381 57 0 165 1271 1587 1351 911 910 0\n1739 -123 290 40 345 340 48 161 42 0 58 497 1712 564 525 522 1461 1552 1538 1299 1307 155 1298 1306 1536 660 1604 168 0\n1740 -32 17 37 81 -147 408 34 35 48 42 28 384 0 518 1684 929 1274 57 54 107 737 1374 928 1354 977 923 917 978 924 1353 1569 1601 1602 42 177 179 180 1734 0\n1741 -17 -145 48 42 28 57 0 516 1701 972 119 155 760 1573 1536 1370 166 1604 966 168 967 1731 1609 169 226 0\n1742 32 17 450 53 34 -104 28 -160 0 349 1660 1301 1510 1295 1509 1551 333 484 1100 1096 1097 1420 1612 42 169 1731 0\n1743 186 33 -154 38 40 -451 5 -270 378 2 0 525 1685 60 157 844 1115 1431 1631 163 148 465 1610 906 291 903 904 0\n1744 33 29 -154 38 35 206 -451 5 -270 378 28 2 0 176 1743 1564 1609 265 1608 263 186 173 185 172 1736 0\n1745 -29 17 384 0 42 44 1353 1354 917 0\n1746 -29 384 0 166 1745 1573 155 0\n1747 198 33 -220 29 28 0 168 257 1731 170 0\n1748 33 34 35 116 -220 165 -451 5 -270 48 161 42 28 121 384 122 2 0 1613 1349 1746 1747 1589 1604 174 1536 1744 155 1538 1461 58 1375 1731 108 1460 96 1282 1740 0\n1749 154 -32 143 34 35 116 165 48 161 42 28 121 384 122 0 168 1604 1536 155 1538 1460 1461 96 1282 58 1740 1375 0\n1750 66 219 276 161 384 -160 0 531 1681 1136 1730 499 1268 1354 917 918 292 185 1547 351 1638 1662 473 328 1503 0\n1751 -33 -154 179 384 0 169 742 214 1354 918 917 0\n1752 -177 33 178 29 28 0 1567 213 170 168 1731 0\n1753 179 -154 -451 12 5 -177 28 384 2 0 1567 170 1746 1564 214 1751 157 1752 218 176 1498 1115 174 163 1431 210 148 0\n1754 -312 -450 164 -306 113 0 1678 1677 495 1697 489 496 1673 1701 1702 490 533 534 1427 0\n1755 -88 448 53 211 164 276 -177 50 42 -306 113 0 181 1555 1593 171 1594 172 1567 170 333 1285 1645 484 1173 354 1100 1737 1096 1754 516 116 1289 1476 1472 148 179 277 0\n1756 -83 -161 381 2 0 328 733 1617 1350 913 910 0\n1757 -255 184 440 -265 287 0 1631 1647 392 454 842 837 1683 1588 1080 1076 1075 0\n1758 211 -463 38 40 -214 -42 2 0 178 1578 157 1570 151 1598 29 286 277 187 148 1478 0\n1759 -177 -208 29 28 0 1598 1601 1570 214 1752 169 0\n1760 -124 373 105 0 498 1267 1680 899 900 894 0\n1761 -143 -104 -160 0 1301 797 1509 1295 0\n1762 -184 343 48 143 42 393 0 1557 1562 1572 1573 1574 1536 1593 1594 165 166 170 938 1596 1604 171 172 937 168 660 1731 333 1285 1303 1511 110 169 1645 1304 129 177 1590 254 1173 944 268 181 179 1737 1289 185 1472 0\n1763 -67 152 394 153 159 0 314 1264 1625 959 953 949 0\n1764 -143 -160 0 1727 1324 531 1717 1530 1761 836 668 1561 184 0\n1765 -42 45 -451 389 82 5 143 -58 0 178 694 1570 1578 1583 1535 151 157 163 932 176 931 1115 112 1286 936 98 508 527 1714 0\n1766 -144 225 219 276 393 -160 139 -58 59 0 531 1717 306 1641 329 1271 114 515 1722 546 867 490 834 484 10 1559 333 706 938 943 937 0\n1767 -35 211 -172 276 27 143 -58 48 0 1606 306 1617 998 171 690 1580 1593 303 878 162 874 204 868 873 182 1716 875 1380 1658 993 862 1000 627 0\n1768 -160 -194 139 145 -58 48 59 0 1587 306 1641 1008 329 1617 1271 531 1727 1764 698 1717 1324 1362 1120 1553 349 718 1620 1660 408 1116 836 327 933 1110 1606 203 299 181 1765 1767 1386 1002 1018 515 1766 546 1618 490 942 10 937 142 938 1559 0\n1769 -170 42 165 -105 139 145 -58 0 306 1641 350 427 942 1526 1008 1271 1559 1593 938 1534 937 515 947 0\n1770 -105 139 145 -58 48 59 0 306 1641 1008 329 1271 350 1726 1526 1661 427 1319 1116 942 668 530 1675 1716 1120 836 536 1110 1606 1541 1769 142 10 490 709 1673 546 946 515 937 1018 1360 941 1002 168 1284 700 129 1386 1589 171 690 174 1163 1580 303 1737 162 868 1550 1667 326 341 1634 1635 337 338 1174 0\n1771 139 145 -58 48 59 0 306 1641 1008 329 1271 1770 1545 531 1727 1764 1768 1717 1324 1003 853 1362 1002 1678 1018 921 112 114 515 1746 546 490 10 142 706 1559 170 938 1731 937 107 943 0\n1772 -144 -10 -451 276 -392 5 -160 -139 28 0 942 1649 1036 511 1678 921 1262 1354 917 918 1567 170 1746 112 114 515 1731 1692 107 168 1721 943 1040 866 1289 743 1033 1610 1750 1396 163 1611 1612 185 1609 252 1608 157 176 151 1115 0\n1773 -90 19 -198 26 -424 -10 -451 276 5 -160 -139 0 511 1678 921 1262 1289 743 1396 1750 185 1612 1608 169 252 151 176 1115 0\n1774 -32 -311 -10 -392 27 -160 42 -139 413 48 0 942 1649 1692 1721 866 1610 163 1036 1040 1033 1700 1095 531 1717 1120 1727 1324 1553 349 1620 1116 1110 1648 1660 718 511 1678 921 1262 1354 917 918 1567 107 168 1604 253 182 278 177 179 1381 993 1000 1695 865 1609 157 1773 943 334 1287 1647 1417 1093 1090 0\n1775 -311 17 -392 -160 -139 -58 48 0 511 1678 921 1262 1354 917 1353 1727 1324 1553 698 1746 1271 918 1759 178 1567 170 306 1617 998 1722 1106 1774 1731 1742 169 188 1612 0\n1776 32 -104 143 -139 28 0 349 1660 511 1678 921 1746 1262 1354 917 918 1759 178 1567 170 1696 488 660 1731 169 782 1590 1612 188 1097 292 1755 185 0\n1777 219 -414 88 -10 276 -392 -160 384 66 145 0 942 1648 969 1000 1695 972 966 1727 1324 1354 917 918 292 1750 185 743 1368 943 1283 334 1001 1666 523 867 1710 0\n1778 -160 143 -139 145 -58 48 0 511 1678 921 1746 1271 1262 1354 917 918 1759 178 1567 938 306 1617 998 328 1641 531 1268 1727 698 1681 1717 1324 1136 492 1120 1553 1362 1730 349 1305 718 937 1620 1660 408 1762 309 1116 327 155 1110 1353 1772 885 1775 1776 107 168 1604 253 182 278 177 961 1381 993 1777 1612 880 851 879 423 883 343 740 28 1367 1266 960 1518 963 1656 0\n1779 143 -139 145 -58 48 0 511 1678 921 1262 1354 917 918 1555 1593 950 1746 1271 1759 895 1567 938 306 1641 1778 1545 350 1726 1525 427 1319 308 942 1655 937 343 947 1527 515 1531 0\n1780 -143 0 1526 1764 1724 0\n1781 145 -58 59 48 0 1780 1771 1779 0\n1782 -105 201 208 -306 48 0 895 178 1678 350 1310 1726 1525 1627 1319 308 1334 668 1521 1655 568 530 1302 1309 1508 343 861 1716 1527 1680 1533 712 1739 532 0\n1783 68 106 397 17 -451 82 5 -270 -455 125 159 69 450 384 66 90 53 83 28 2 0 1354 917 1353 918 1518 1656 963 960 1367 60 1276 740 1753 1608 185 1547 1419 1277 1096 1100 1654 342 445 1131 341 0\n1784 106 397 2 17 -451 82 5 -270 -455 125 159 69 450 384 66 90 53 83 28 0 1783 62 63 1366 1367 960 0\n1785 -139 -145 249 28 114 2 48 0 1780 516 1702 534 1701 533 1673 490 123 121 120 328 511 1262 1678 1696 1354 496 1677 921 488 917 495 1746 1427 918 1555 1759 1593 178 1782 1545 531 1268 1727 1681 1717 1324 499 1136 1120 1553 1730 349 718 1776 1620 408 168 1116 327 1604 1110 1536 278 155 961 1353 744 1784 0\n1786 66 212 17 -451 82 5 -270 450 384 -455 125 159 69 -145 83 28 2 0 121 120 1354 917 918 1353 278 744 961 1784 0\n1787 106 -469 54 -449 50 88 82 276 105 109 90 53 83 77 0 1100 1666 334 1545 531 1681 499 1268 1547 1421 532 1277 89 352 1686 1488 1664 478 1065 93 321 320 1728 1062 0\n1788 17 82 105 -170 -145 83 28 114 77 2 48 0 1780 1545 531 1717 1120 1727 1324 1553 349 1620 1116 1110 1660 1194 718 516 1693 1681 557 495 1701 533 1673 490 1702 534 123 561 496 632 488 1427 921 1136 1730 499 1268 1593 171 1559 122 121 120 119 1742 107 168 1604 253 274 887 178 1786 43 746 1420 1096 1100 1654 889 856 886 1674 565 893 491 497 131 135 1492 1190 1191 1787 71 1749 1748 742 0\n1789 -58 48 59 0 5 8 9 306 1271 1617 1641 328 329 1781 119 516 1673 1701 490 972 1785 10 142 707 1593 1545 171 531 1727 1681 1324 561 1553 921 349 1746 408 327 1788 155 760 1562 1595 1369 1594 1759 173 966 172 178 967 1536 1609 269 1596 226 177 176 169 1732 0\n1790 -17 -3 105 -145 48 0 142 1593 171 11 516 1545 531 1681 561 921 1746 1701 972 119 155 760 1562 1595 1369 1594 1759 173 966 172 178 967 1536 1609 269 1596 226 177 176 169 1732 0\n1791 -37 -464 94 88 17 248 249 61 58 0 1780 78 80 81 82 1356 1358 923 926 928 1630 326 337 1635 402 403 341 342 1174 1480 336 305 431 0\n1792 -36 77 88 17 105 276 -145 0 1780 516 1693 1545 531 1681 557 495 1701 533 1673 1671 489 490 1702 534 123 561 496 632 488 1427 122 120 51 52 53 172 1376 1576 1581 1594 156 162 149 1372 1420 977 1096 980 1374 473 326 351 1629 1421 478 352 0\n1793 -40 207 -198 -104 113 291 470 -145 0 516 1693 557 495 1701 533 1673 1671 489 490 1702 534 123 561 496 1427 176 785 1613 1191 301 1190 1097 1096 1100 1654 856 1674 565 491 497 1492 0\n1794 107 -33 77 -3 105 -145 48 0 1780 1545 1727 1324 142 1559 516 1693 531 1681 557 495 1701 533 1673 1671 489 490 1702 534 123 561 496 632 488 1427 11 119 120 1553 1790 1742 168 253 887 169 1612 1097 1096 1100 1654 889 886 893 135 856 1674 491 1604 274 178 1593 171 921 122 1421 1423 71 742 1749 0\n1795 77 37 -3 105 276 -145 48 0 1194 1545 531 1681 516 1701 632 488 1727 1324 1553 1693 557 495 533 1673 1671 489 490 1702 534 123 561 496 1427 11 119 120 1790 1742 168 142 1559 253 1793 887 177 107 1593 171 921 1746 1334 1792 1732 1023 169 1612 1097 1096 1100 1654 889 434 886 1024 893 1021 1025 1684 929 1794 352 764 478 1356 926 923 0\n1796 -3 105 249 -270 -145 48 59 0 516 1545 531 1681 561 921 1746 1727 1324 1553 718 1693 557 495 1701 533 1673 1671 489 490 1702 534 123 496 632 488 1427 1620 1116 1717 1120 1110 1136 1730 1334 1627 499 1268 408 327 328 1660 1194 309 122 120 119 1789 11 142 1559 1593 171 1790 1538 1742 107 168 1284 1589 1604 253 1163 177 1737 1791 1793 1795 6 323 1786 1623 1628 1633 43 737 837 475 305 1420 261 352 1096 172 1422 1732 71 742 1461 0\n1797 219 28 3 -160 -270 -145 58 59 0 1780 516 1693 531 1681 557 495 1701 533 1673 1671 489 490 1702 534 123 561 496 632 488 1427 921 1334 1627 1620 309 1660 122 1097 1096 1100 1654 483 484 342 434 445 329 333 337 341 10 1551 1262 168 1284 1425 1750 1589 319 532 1163 1651 1686 1737 338 1335 1480 1616 305 0\n1798 -449 28 105 249 -270 -145 48 59 0 516 1545 531 1681 561 921 1746 119 1789 1796 1797 1612 169 1731 168 1589 1163 1737 1620 1717 836 1606 299 249 171 1660 1194 1701 632 488 1727 1324 1553 1597 1793 1284 107 177 1334 1627 408 309 1673 1671 489 490 122 1100 483 329 10 1262 1785 1425 6 76 1792 1791 1732 0\n1799 -177 35 40 33 41 28 29 248 249 61 34 58 48 0 1731 168 1589 1163 1737 1604 1284 107 1594 1759 172 178 1732 1536 1791 155 0\n1800 28 105 249 -270 -145 48 59 0 1796 516 1545 531 1681 561 921 1746 1693 557 495 1701 533 1673 1671 489 490 1702 534 123 496 632 488 1427 1620 1717 836 1606 1727 1324 1553 408 1660 1194 309 120 119 1789 1797 1597 1612 299 177 169 1731 168 1793 249 171 1798 1096 1799 149 1562 1420 155 0\n1801 105 249 -270 -145 48 59 0 516 1673 1671 915 489 1693 1789 1545 531 1681 557 495 1800 165 1738 1586 1587 305 1588 141 1633 148 323 1546 1544 1260 0\n1802 -28 280 58 0 915 489 165 1738 1586 1587 305 1588 141 1633 148 323 1337 1544 1676 1260 495 1546 0\n1803 -105 -270 -145 48 59 0 1620 1116 1660 1789 516 1673 1671 1802 915 490 350 1269 1726 707 1627 470 1319 1123 308 668 1730 530 1675 1716 1120 836 868 1110 1606 303 1541 1346 1540 1521 1525 1539 511 10 329 1263 1270 1641 913 910 1350 39 1446 497 1712 637 525 532 1461 0\n1804 -270 -145 48 59 0 1780 1789 516 1673 1671 1802 976 1702 1701 123 122 120 119 1620 1660 1116 1194 1803 1545 1801 531 1727 1617 1638 1639 1681 1717 603 632 1324 1615 351 352 865 561 1120 488 1553 305 1422 1609 921 1110 1754 718 1371 1096 157 1746 973 1097 974 1597 1612 1593 177 169 171 1731 107 168 1604 1793 274 178 1741 1420 1419 149 185 1594 1608 172 151 1732 1115 78 80 82 163 1356 1358 1610 923 866 928 481 326 0\n1805 -289 147 140 332 0 1712 637 525 532 1461 0\n1806 -145 48 59 0 1789 516 1673 490 1671 915 1802 1804 349 668 530 1324 1675 1716 1727 1120 1545 350 1269 707 1627 1661 1123 1116 1730 1110 1541 1346 1540 1521 1539 1805 497 1508 1678 511 10 329 1263 1270 1641 1446 913 39 910 1350 0\n1807 121 306 123 124 42 28 283 5 -456 61 125 145 59 0 1780 511 492 1446 1447 1263 515 546 599 490 524 10 28 703 0\n1808 -98 -3 138 -2 136 123 124 -456 125 145 0 1780 692 703 1448 0\n1809 -3 -2 136 299 -105 145 48 0 1780 697 1726 1319 668 530 1716 350 1661 1116 1675 1120 1110 1541 1540 1346 1521 1539 1805 497 492 1627 1123 1730 1269 142 1593 950 1808 1527 524 1531 1711 592 515 491 509 1456 0\n1810 -2 -105 48 59 0 1780 1726 1319 668 530 1716 350 1661 1116 1675 1120 1110 1541 1540 1346 1521 1539 1805 1806 1269 309 1627 1123 1730 719 1789 1334 1668 1670 1802 497 1508 1678 1807 495 555 508 1676 511 1270 697 1809 10 490 546 515 1448 509 692 592 1527 524 0\n1811 -105 48 59 0 1806 1789 350 1269 1726 1627 1661 1319 1334 1123 309 1116 668 1668 1730 530 719 1670 1675 1716 489 1802 1120 1110 1541 1346 1540 1521 1539 1805 497 1508 1678 1807 495 1261 1676 1810 1544 505 0\n1812 144 136 42 140 425 138 299 2 124 123 5 -104 283 145 58 0 1780 1691 511 505 349 1620 309 492 1454 509 776 1721 543 592 1040 489 524 1033 1544 28 1396 1261 343 185 1405 1626 1608 1052 1051 1050 0\n1813 136 42 307 140 425 138 299 2 124 123 5 -104 159 283 145 58 0 1780 1691 511 505 1812 515 599 600 524 525 1455 0\n1814 -303 -287 140 305 159 145 0 1705 518 510 1714 591 622 523 525 1459 0\n1815 136 138 274 299 2 42 124 123 5 -455 159 283 69 145 58 48 0 1780 1036 1337 1623 312 1691 511 505 1362 1553 1305 1762 155 1538 1813 1812 1683 1698 515 501 837 1692 599 1548 1554 1588 1721 543 524 759 1587 166 866 1802 1455 853 1591 61 63 1624 170 1733 313 168 1436 1589 314 1343 379 0\n1816 153 66 152 65 138 140 42 215 61 276 5 -455 117 159 69 145 0 28 343 1626 315 1436 57 314 1763 1459 380 950 750 341 303 1552 868 522 1723 0\n1817 299 2 42 124 123 5 159 69 -327 145 58 48 0 1780 1362 1553 1305 1762 155 1538 1717 349 1620 836 1606 309 1660 1681 1136 1730 1334 1627 492 505 1691 1337 593 511 1623 480 510 312 1815 508 591 1814 523 837 1554 1587 853 1624 313 1816 524 1266 599 592 1436 515 509 1499 57 1457 0\n1818 -67 404 107 106 439 85 312 -153 42 105 145 48 0 1780 524 1711 491 31 1545 1727 1324 1362 1553 1305 1762 155 1538 531 1717 1120 349 1620 1116 1110 718 492 55 314 1656 344 1412 1075 1080 1413 1414 1683 112 515 60 61 750 501 1692 1699 546 1548 1721 1032 976 759 973 1029 974 1028 1559 1395 852 87 1649 1115 866 163 1610 0\n1819 65 305 -153 121 42 48 59 0 1780 1693 1266 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 349 1660 531 1681 1136 1730 1717 1268 1546 148 1279 1554 1565 1588 1587 848 1076 165 1003 1617 1638 1639 1615 351 352 305 1371 1818 1436 43 313 1262 1624 329 1008 1002 1018 114 515 784 1722 546 1420 1106 490 1096 10 1100 706 484 1438 333 0\n1820 -65 282 138 2 283 145 58 0 1780 312 1260 1623 323 1069 1544 1729 489 1671 1697 543 542 546 511 509 508 515 1072 0\n1821 -66 144 415 145 0 1780 313 1262 1624 1018 1008 1002 0\n1822 144 415 439 85 65 116 68 140 276 -455 117 69 145 0 1780 1413 1075 1821 1436 55 314 1656 473 344 351 1412 0\n1823 66 122 -144 439 29 28 329 85 65 116 68 2 140 -451 5 -270 -455 159 69 145 0 1780 114 112 1660 1362 1436 41 55 314 149 741 473 1567 351 170 938 1412 1731 937 1075 107 168 942 1414 943 1589 1648 750 743 174 865 1349 1609 1743 0\n1824 -153 138 113 121 2 42 48 59 0 1780 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 1538 531 1717 1120 349 1620 1116 1110 1660 718 1681 1136 1730 492 499 1268 1789 524 1266 1680 1711 491 1820 1546 1819 148 1279 1672 1695 1554 1565 1588 489 1802 1587 164 166 1076 1003 1822 113 114 115 515 1699 1700 546 560 526 527 490 496 1487 1823 43 313 1262 1484 1624 1181 329 1185 10 1659 142 706 333 1559 943 938 937 0\n1825 -66 115 3 28 59 0 313 1262 1624 10 329 0\n1826 -144 -9 65 153 138 2 42 48 59 0 1780 148 1554 1587 165 1588 1076 166 1279 1811 1545 531 1717 492 1727 1324 1553 349 1620 309 718 28 343 1626 315 1806 1362 1305 1762 155 1538 836 1606 1120 1116 1110 1660 1681 1136 1730 499 1268 515 784 703 1692 1722 546 543 1106 490 915 1825 1816 1436 523 752 55 314 1674 1656 473 491 344 351 1412 1547 1075 532 1756 1414 636 61 732 496 921 962 1784 41 743 0\n1827 65 153 138 121 2 42 48 59 0 1780 1811 1545 531 1717 492 1727 1324 1553 349 1620 309 718 28 343 1626 315 1806 1362 1305 1762 155 1538 836 1606 1660 1681 1136 1730 1268 1546 148 1279 1554 1588 1587 1076 1003 1826 1821 1822 1816 491 523 1674 0\n1828 138 113 121 2 42 48 59 0 1811 1545 1727 1324 531 1717 1806 1789 1824 1827 312 1260 1820 1623 1674 323 1069 523 1544 1729 489 1697 1703 511 517 1074 0\n1829 -65 114 2 58 0 312 1260 1623 1544 323 0\n1830 -98 259 -441 243 415 439 85 65 28 329 83 140 48 59 0 1780 338 1811 1545 1727 1324 1553 349 1660 1308 531 1681 1136 1730 1717 492 1268 1806 343 1517 1626 404 1507 315 327 1822 1414 114 515 703 525 1276 546 1685 990 490 991 986 1825 987 1441 1609 342 865 447 0\n1831 -231 -9 65 28 329 83 2 42 48 59 0 1780 148 1554 1587 1003 1588 1076 166 1279 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 1538 531 1717 1120 349 1620 1116 1110 309 1660 718 1681 1136 1730 492 1268 1623 1643 1078 854 1075 1683 501 842 1548 1651 338 1830 28 524 1266 1680 1711 491 1822 1414 114 515 784 759 61 732 1699 1722 546 560 1029 1032 1106 490 496 1028 1823 1030 43 1825 442 1420 706 341 1096 1442 1100 342 1654 0\n1832 -153 179 26 34 19 231 415 439 29 85 65 28 140 -451 276 5 -455 117 69 145 0 151 524 1266 1680 1711 840 491 382 1822 112 515 1115 1731 1700 176 168 862 252 1590 0\n1833 2 42 124 123 48 59 0 1780 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 1538 531 1717 1120 349 1620 1116 1110 309 1660 718 1308 1681 1136 1730 492 1334 1268 1789 1817 1676 1688 495 488 1828 102 104 105 510 1672 1695 489 1802 1399 1829 1546 148 1279 1554 1588 1587 166 1076 1003 1831 1622 385 384 1036 865 1033 1609 1034 1396 157 1591 1610 185 170 938 163 1608 937 1051 1832 28 343 1517 1626 1507 315 1052 1822 1050 112 114 1404 1731 748 107 943 0\n1834 -144 -98 231 -2 48 59 0 1780 343 1626 141 1587 165 1811 1545 696 1270 531 1681 1136 1730 1727 1324 1553 1717 1268 515 703 546 490 1825 10 1503 1776 379 168 1343 1589 0\n1835 153 231 65 230 -2 42 48 59 0 1780 141 1587 1003 165 1811 1545 696 1270 1727 1324 1553 349 1620 309 718 1308 531 1681 1136 1730 1717 492 1268 1806 28 343 1517 1626 1655 1507 315 308 1834 1821 1436 1503 1264 1625 379 378 336 339 1343 338 1589 1440 168 133 715 660 1776 1763 19 701 950 10 1593 142 0\n1836 144 82 68 98 231 -2 -104 105 145 0 1780 141 1587 1003 165 1545 696 1270 531 1681 1136 1730 1268 1821 1518 1625 379 336 1343 1016 1589 1002 168 1018 1776 0\n1837 231 65 230 -2 42 48 59 0 1780 1811 1545 531 1681 1334 384 141 1587 1003 165 1806 1727 1324 1362 1553 1305 1762 155 1538 1717 1120 349 1620 1116 1110 1660 718 1136 1730 492 1268 385 1036 1835 31 524 1266 691 1680 1836 112 114 515 1692 560 1721 556 921 1040 866 495 837 1746 1033 1591 1610 1546 1819 1588 170 938 163 1279 1695 1076 1731 937 865 107 1609 943 157 1289 1832 1396 1608 185 0\n1838 -153 259 -73 -441 121 65 273 -2 42 48 59 0 1780 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 1538 531 1717 492 524 691 1819 1711 1695 491 865 1414 1413 1609 61 525 1276 114 515 759 987 1685 1699 1029 991 1032 1028 986 1030 990 442 341 0\n1839 65 230 -2 42 48 59 0 1780 1811 1545 531 1681 1334 384 141 1587 1003 165 1558 994 696 1806 1727 1324 1362 1553 1305 1762 155 1538 1717 349 1620 836 1606 309 1660 718 1308 1136 1730 492 1268 1837 1623 1643 1337 330 1078 1676 495 1546 148 1588 1076 854 1075 1683 501 842 1548 1651 1838 28 343 1517 1830 404 1507 1695 327 1413 510 1000 515 703 993 546 1382 490 133 1825 1816 0\n1840 -32 370 82 -98 153 113 -2 -104 -160 0 1780 1308 1268 1727 1324 141 1587 1003 696 531 1681 1136 1730 1517 107 168 249 171 950 1516 0\n1841 153 -65 -2 42 48 59 0 1780 312 1623 1337 1688 488 38 141 1587 1003 165 1811 1545 696 1270 7 1806 1727 1324 1362 1553 1305 1762 155 1538 349 1620 309 718 1308 531 1681 1136 1730 1717 492 1268 28 343 1517 1626 1655 404 1507 315 1046 327 1402 1042 1043 1560 177 887 1840 660 1776 333 1285 1391 1644 1645 1505 1002 338 1173 1625 1008 1737 336 1624 1389 313 1287 1441 1474 133 701 1504 10 0\n1842 -35 139 -88 -2 59 0 141 1587 165 1270 171 701 1593 10 142 0\n1843 -3 35 32 96 82 -153 29 9 28 83 42 -160 48 0 1780 660 333 1645 1173 1737 1644 338 1285 1266 531 1681 1136 1730 1268 142 706 702 1559 1442 170 129 1731 1474 169 181 1590 0\n1844 32 96 -65 -2 42 48 59 0 1780 1841 691 1266 1280 38 141 1587 1003 165 1811 1545 696 1270 531 1681 1136 1730 1727 1324 1553 1717 1268 1806 660 1776 1842 1364 1843 10 490 1704 546 957 515 949 1821 953 1518 1625 0\n1845 139 -417 88 -2 48 59 0 1780 141 1587 165 1270 1806 1811 1545 1727 1324 1362 531 1717 1018 114 515 546 490 10 142 706 1559 943 938 937 0\n1846 96 230 -2 42 48 59 0 1839 1841 524 1711 491 691 1266 31 141 1587 1003 1811 1545 696 1270 1727 1324 1553 349 1660 355 1620 531 1681 1136 1730 1268 1844 107 168 1390 249 1002 171 1845 13 18 1262 1518 378 338 1441 342 715 1619 1519 308 0\n1847 230 -2 42 48 59 0 1780 141 1587 1003 1270 1811 1545 1727 1324 1553 349 1660 355 1620 1305 1839 1841 31 524 1266 691 1711 491 1846 341 710 1304 365 1303 308 1551 1390 168 1002 249 1845 171 13 18 1519 0\n1848 -139 35 -198 -230 28 42 -160 145 48 0 1780 1604 1621 1336 1682 1642 1078 1727 1324 1362 1553 1305 1762 155 1538 531 1717 1120 349 1620 1116 1110 1660 718 492 511 1262 1678 1354 921 917 1746 918 1353 1567 1594 278 170 938 253 172 179 937 177 1077 1772 1075 1080 1413 1683 491 842 548 1651 858 433 0\n1849 -32 -2 42 48 59 0 1780 1847 1621 141 1587 1003 165 1270 1806 1811 1545 1727 1324 1362 1553 1305 1762 155 349 1660 355 1789 107 168 1284 1589 249 1163 171 1737 1848 1845 1002 1008 1390 1388 1640 390 31 334 305 319 1841 1646 1647 1548 345 466 346 467 758 352 353 1482 0\n1850 42 124 123 48 59 0 1780 1811 1545 1727 1324 1553 349 1620 309 1660 718 1305 1806 1362 531 1717 492 1762 155 1538 1833 141 1270 1587 165 1847 1621 1642 1628 1336 1078 1337 1682 1676 495 1849 660 1776 333 1303 1644 484 1304 1844 1546 148 1588 1076 854 1075 1683 545 1081 501 842 490 1548 477 10 1838 703 28 0\n1851 -208 -104 -160 145 0 1780 531 1717 1120 349 1620 1116 1110 1660 718 1570 1578 1583 1599 1535 151 157 163 176 1115 169 782 1612 214 226 188 149 155 1430 142 706 1559 198 170 168 116 660 354 333 484 0\n1852 48 59 0 1780 1806 1811 1545 531 1727 1681 1324 1553 1362 349 1305 1660 1851 178 895 1762 1760 155 1850 1538 58 497 1712 565 525 523 1459 1461 104 510 1283 69 532 1277 1695 1368 1686 972 1065 966 1728 969 1639 1648 1663 1664 478 408 335 426 481 321 320 327 334 326 1407 1062 319 333 391 0\n1853 -123 -96 140 99 124 -48 0 184 1571 151 58 497 751 1712 525 1461 59 753 0\n1854 -264 267 266 -160 59 0 1852 1655 450 451 308 305 306 1501 0\n1855 -60 90 -262 -88 -160 -48 0 333 1645 443 346 1644 442 345 1173 1737 339 338 1285 531 1681 1136 1730 1268 184 1561 1111 1529 1579 157 1571 151 137 22 308 717 1619 1473 342 38 1444 0\n1856 -57 272 116 123 165 -471 -327 0 1780 3 305 1615 1616 1633 1617 1335 1337 1686 1687 1676 864 534 633 495 1585 489 848 1493 1695 533 0\n1857 -320 60 90 -153 123 100 165 -471 -88 145 -160 42 59 0 1780 333 1645 1173 1737 1644 338 1285 107 531 1681 1136 1730 1268 1852 184 1561 1111 1529 1605 189 1579 157 1571 151 144 138 137 1680 1711 840 491 1662 1856 1501 5 9 306 1271 698 693 1617 1641 1385 328 998 1008 1002 1445 1017 129 133 1696 1477 1379 488 39 993 1000 1001 1695 105 533 1493 0\n1858 -90 29 415 28 2 116 68 276 -88 140 145 -160 -214 0 333 1645 1173 1737 1285 107 531 1681 1136 1730 1717 492 1268 1561 1111 1529 1579 157 1571 151 144 118 1289 1731 1478 112 38 148 1279 1822 1588 1076 0\n1859 90 123 165 -262 -471 -88 145 -160 42 59 0 531 1717 492 1852 720 184 1561 144 333 1644 442 1645 443 1854 343 28 524 345 1855 1857 0\n1860 -58 -90 116 68 276 -88 140 145 -160 42 -214 0 1289 333 1645 1173 1737 1285 107 1561 1111 1529 1605 189 1579 157 1571 151 144 5 1271 1478 1385 148 1858 1588 166 0\n1861 276 -88 140 145 105 42 59 0 333 1645 1173 1737 1644 1285 1545 531 1681 1334 1614 1852 184 1561 1717 836 367 344 1136 1730 492 720 1268 137 1346 1521 1111 1529 1605 1191 1579 157 1571 151 144 1194 868 1190 1723 522 664 341 786 442 443 1853 1854 343 28 1266 524 1680 1711 840 491 1662 1856 1859 706 1860 1501 22 26 717 1364 1473 1471 956 949 38 52 957 1436 1703 1704 1802 490 1825 0\n1862 35 41 -466 46 -88 17 145 42 -214 0 333 1645 1173 1737 1285 107 1538 1561 1111 1529 1579 157 1571 151 1473 1471 148 1279 172 739 1554 1588 1594 1587 166 149 165 1003 41 1485 1821 117 112 1731 0\n1863 41 -466 429 165 46 110 -88 17 145 42 -214 0 333 1645 1343 1577 156 107 1605 189 1862 20 171 1568 1580 1592 150 162 1594 1045 149 1042 1485 1046 781 1619 128 342 0\n1864 -88 17 145 105 42 59 0 1538 1545 531 1717 1852 184 1561 1111 1529 1571 333 1659 1185 1861 1667 341 1552 522 787 778 1708 1723 549 1188 536 1048 1181 1863 177 1569 1597 188 1485 149 1537 1567 170 0\n1865 -282 370 219 140 -160 42 -48 0 1780 531 1681 1334 1614 184 1561 1717 836 367 344 1136 1730 492 720 1268 137 1346 1521 1111 1529 1571 1051 144 1605 1674 1711 549 892 524 522 886 28 664 889 343 341 1853 1654 1626 867 315 1052 380 840 1722 1050 314 1718 611 515 532 518 1405 1461 40 525 1436 1712 313 839 472 293 864 0\n1866 234 -471 318 123 165 -96 116 17 283 179 0 1780 341 1538 380 840 314 980 1690 1718 611 1721 543 532 518 534 489 1461 1494 525 749 79 1275 1712 50 983 172 977 1581 1594 162 149 1372 0\n1867 328 233 272 -332 140 220 0 532 643 864 518 293 1461 839 525 1712 0\n1868 -263 -161 35 100 67 57 102 219 145 -160 42 59 0 531 1681 1136 1730 1268 1852 137 1619 1654 308 867 1501 1722 5 9 306 1271 515 1352 360 1386 1756 326 1821 1443 0\n1869 -178 100 67 57 106 110 102 165 41 -32 145 -160 42 59 0 168 1589 1343 1852 184 1605 301 531 1681 499 1268 189 137 1568 293 171 185 1547 1277 1868 342 440 128 328 1542 1496 118 0\n1870 233 57 272 -332 110 102 123 165 41 -32 140 145 -160 42 59 0 1780 351 1852 184 1561 531 1717 836 1620 1681 1605 138 314 980 1867 1686 1335 459 345 1869 978 839 977 1689 1376 495 557 1814 0\n1871 -145 -327 -471 116 165 123 0 1681 123 516 1673 1693 1701 1702 561 490 1671 557 533 632 534 496 489 495 488 1492 0\n1872 -48 75 351 130 151 -129 100 0 502 1713 526 184 1316 1579 1315 157 664 86 763 0\n1873 -160 48 17 -59 113 32 0 1780 307 1618 942 14 531 1727 708 1324 1360 1553 937 946 1362 603 120 123 1742 1754 0\n1874 33 123 -88 -48 -59 0 1780 137 15 307 1650 336 1618 335 333 1659 452 343 422 342 1012 107 184 1605 189 138 17 14 1384 1002 1017 1678 921 1746 1731 119 708 1391 1545 524 1508 1680 498 0\n1875 -33 -88 -48 -59 0 307 333 1659 452 897 1645 1173 1737 1285 184 1561 1111 1529 138 169 704 1590 901 894 895 1346 273 1758 141 0\n1876 -88 -48 -59 0 184 1605 189 137 307 1650 336 1618 335 15 14 107 333 1659 422 452 342 343 1012 1875 1384 1874 1002 58 497 1017 1679 1712 1678 857 525 921 1568 1746 1752 1731 918 917 1354 48 745 1461 0\n1877 -123 88 -48 257 0 1780 1551 168 1589 1343 438 1337 1676 184 1561 1111 1529 1571 1051 151 56 58 497 1679 1712 857 525 1575 1592 225 261 155 837 1538 1643 1805 1461 1078 1723 532 753 522 1718 1552 498 1055 341 751 59 1050 344 1631 1636 1757 321 394 327 402 334 320 1054 326 0\n1878 -417 124 -59 145 -48 0 1780 184 1605 1876 1551 168 301 188 307 1618 335 1650 1877 17 1017 1018 1678 515 783 1508 1722 1545 535 708 116 0\n1879 -161 -59 145 -81 -48 0 1780 307 1650 1876 1551 168 1589 1343 438 1337 1676 1163 1737 184 1605 301 188 336 1618 335 15 326 1629 1657 345 1658 346 1635 338 1634 337 95 1571 137 71 532 1686 1718 1335 498 840 1616 1626 305 343 1387 1878 1002 1003 1586 1588 837 454 344 1175 342 779 1619 1654 447 360 354 352 306 116 1481 1288 0\n1880 -59 312 -81 140 154 -48 0 1780 516 307 1876 1618 1551 852 1567 918 1879 1461 518 737 1706 1354 921 917 0\n1881 -32 178 85 -147 140 0 518 1706 921 1746 496 168 737 213 41 149 0\n1882 52 139 -88 9 59 38 -214 0 333 1645 1173 1737 1561 1111 1529 1579 157 1571 151 144 1475 1478 1842 0\n1883 138 132 145 136 159 139 154 140 0 1780 1455 1458 524 491 1711 0\n1884 -147 312 -81 140 154 -48 0 1780 1880 516 326 1658 96 94 138 1367 184 518 730 1705 1706 1344 495 872 496 921 869 1546 1746 871 1260 1643 454 330 963 960 961 1601 1881 660 736 41 1262 1882 102 1883 0\n1885 138 147 145 136 140 154 159 0 1780 1458 1459 491 523 1674 0\n1886 312 -81 140 154 -48 0 326 1635 96 138 137 516 1884 1461 532 1277 1686 504 1065 1728 1885 104 510 1283 1695 533 1549 352 1648 447 335 342 1064 0\n1887 -161 -138 426 402 259 104 0 1283 104 102 69 532 1277 1396 1368 1686 1033 966 1065 1036 969 1728 1649 447 335 342 1064 0\n1888 -138 -81 140 154 -48 0 1886 1702 1040 1701 972 326 1635 184 1571 1051 137 1887 1349 1461 58 518 730 1705 1706 495 496 1546 734 1347 903 906 1348 1662 754 1052 1404 1050 0\n1889 145 -81 140 154 -48 0 1780 1888 326 96 184 1561 1111 1529 138 1458 1885 24 27 491 518 730 1363 1674 1711 1705 1344 523 524 872 869 959 871 949 1623 953 399 0\n1890 -28 280 0 1271 1802 0\n1891 211 330 -247 -214 0 1658 1561 1111 1529 286 862 866 1707 1665 522 402 1552 341 0\n1892 -29 330 140 154 0 45 1746 921 1355 1706 495 518 635 1461 532 0\n1893 -202 98 128 131 287 76 -198 -145 162 -247 94 104 0 1589 1163 1737 1629 1657 345 1658 346 1635 338 1634 337 1576 261 225 837 155 1623 454 1548 399 344 761 336 1175 1549 342 352 447 0\n1894 147 -81 140 154 -48 0 1886 1673 1671 1890 184 326 1702 1891 1590 169 1889 119 1892 1731 168 1589 1343 1652 1605 301 121 1701 533 1634 1024 95 1571 138 137 1461 532 1277 1686 1718 635 504 1065 574 840 1728 501 1626 343 1893 1022 1021 1394 133 523 1064 1710 328 867 411 0\n1895 -81 140 154 -48 0 138 1367 184 326 1658 1886 1673 1702 1671 1889 119 1890 1891 1590 169 1892 1731 168 1604 1894 518 730 737 1705 1706 1344 1354 872 921 869 917 871 918 454 278 963 961 960 0\n1896 -147 -145 -211 121 29 81 -214 0 1780 1590 169 119 516 1673 1671 1890 1731 107 1345 1603 874 873 878 1282 1561 1111 1529 1605 54 57 58 518 1274 1374 1376 1684 928 977 929 923 978 924 1568 293 295 171 185 186 1736 0\n1897 -145 -211 -247 287 29 140 154 -48 0 1780 1635 1895 1345 1603 874 873 877 1694 859 1595 155 1087 1089 1084 878 1282 97 1590 169 495 184 1561 1111 1529 1571 137 119 516 1673 1701 1671 533 1890 1731 168 1896 1461 69 532 1277 1686 1718 504 574 840 501 1626 1548 343 761 1893 172 1592 1415 171 0\n1898 -35 204 147 145 -136 100 93 92 267 287 140 154 -48 0 1163 1737 184 1571 1461 532 1718 840 1626 343 1686 1335 1616 305 97 346 138 137 23 171 690 1592 259 1351 261 911 837 910 454 915 344 1672 1175 510 133 1459 0\n1899 51 28 147 145 -136 33 100 93 92 267 287 29 140 154 -48 0 1461 69 1282 495 184 1561 1111 1529 1605 189 1735 168 1589 1898 1736 172 731 261 1546 148 0\n1900 -51 147 145 148 37 93 140 154 -48 0 1461 532 1686 184 1605 138 186 1283 295 1459 156 523 765 577 77 502 0\n1901 147 145 -136 -303 33 100 93 92 267 287 29 140 154 -48 0 1694 519 1282 138 1900 1899 1890 1672 510 591 1459 523 0\n1902 -247 287 330 140 154 -48 0 1780 1892 1895 1345 184 1561 1111 1529 1605 1629 1634 1635 1658 1891 1657 337 338 1087 1590 1603 345 169 874 873 877 878 1694 1282 519 1089 1084 1897 1901 54 518 1274 1684 502 77 156 1563 1575 295 293 171 186 185 1415 0\n1903 259 37 444 148 -147 -214 0 518 1684 502 1274 54 1561 1111 1529 1605 338 1087 77 1084 156 1563 1575 295 293 171 186 185 1415 0\n1904 -211 408 -147 247 29 81 -214 0 1780 518 1706 921 1684 929 1274 57 54 1345 1561 1111 1529 1605 1590 1603 169 874 847 873 1694 878 519 1089 1282 1903 1644 333 1551 928 1374 737 923 977 1354 924 978 917 1575 295 293 918 171 186 185 1566 1736 165 0\n1905 -147 393 247 121 29 330 81 399 -48 0 1780 184 58 518 1376 1706 921 1904 286 187 866 1649 942 937 938 1567 918 838 917 1354 1262 737 660 333 1285 1876 1659 1882 455 148 963 277 960 961 0\n1906 -83 -425 -161 0 532 1686 1335 1616 305 71 103 328 1617 1639 306 352 1397 0\n1907 218 147 145 330 140 154 -48 0 1780 1461 532 1686 1065 1728 504 1277 138 1362 1040 184 1605 137 1034 866 1033 1649 335 942 937 938 1574 155 1906 1064 133 342 1459 1654 422 510 1283 354 333 1695 1551 533 972 168 779 1549 1887 301 1651 188 319 116 1548 762 0\n1908 145 287 330 140 154 -48 0 1780 1902 495 1892 1040 1895 1345 138 1367 184 1605 137 1362 1905 1461 69 532 1277 1686 1065 1728 1907 1591 297 938 874 937 873 942 878 1649 1036 1033 1396 101 1289 774 1064 0\n1909 -83 -161 426 0 69 101 1906 1396 1033 0\n1910 -424 -97 50 365 220 0 1780 1034 1396 297 774 874 878 873 0\n1911 -161 -312 164 90 121 330 81 -48 0 1780 1673 1671 489 490 1040 534 1345 184 1571 1051 1605 137 69 532 1277 753 1686 1718 1065 574 1055 1728 501 1050 1909 1064 342 1654 1100 1910 1033 1036 1649 1665 422 327 333 1551 168 301 1097 1096 1428 47 496 1403 1678 314 603 1625 531 446 1545 350 0\n1912 -97 256 122 129 74 123 67 161 114 162 164 121 163 81 140 -48 0 1780 1376 184 1561 1111 1529 1605 1191 129 132 134 342 888 1619 422 308 333 1197 1551 1374 1190 168 977 1494 1491 301 978 491 1865 1556 178 1599 0\n1913 -32 371 408 161 28 34 29 140 154 -48 0 1780 1461 518 1706 921 57 54 1895 184 1561 1111 1529 1571 138 107 737 1374 1354 977 917 978 918 1568 1569 214 171 177 887 169 886 1732 892 893 1282 1674 135 1460 491 0\n1914 287 330 140 154 -48 0 1780 1892 534 1895 184 1571 1561 137 495 1908 119 121 123 516 1673 1701 490 1671 533 489 1890 1911 1461 57 58 518 1274 1896 1376 1684 1706 286 502 496 921 866 1649 1912 891 1913 660 1731 1876 169 199 214 142 918 1825 917 1354 0\n1915 330 140 -48 154 0 1914 1705 635 518 532 1461 0\n1916 161 140 154 -48 0 1780 1915 1687 1335 1632 906 1616 305 1720 1722 515 1719 1718 498 1721 935 1702 516 1895 184 1561 1111 1529 1605 189 1349 1461 903 57 58 518 1274 1539 904 1684 1705 1585 1607 293 929 495 242 295 978 1376 932 924 977 931 923 1374 1373 1359 1357 107 333 1285 1876 1821 76 1645 1003 1864 1173 1587 695 1737 141 1352 1758 1738 1590 1384 169 0\n1917 -147 140 154 -48 0 1780 1916 753 1277 1915 1720 1722 515 1719 1718 498 1687 1065 1728 1721 935 1702 516 1709 1895 184 1561 1111 1529 1579 157 1571 151 144 137 57 58 518 1274 1539 1684 1705 612 1545 929 495 1334 531 1376 1614 1717 836 367 344 59 179 1584 1600 1601 932 1602 978 931 924 977 1359 923 1374 1373 1357 333 1285 1876 1821 76 1645 1003 1864 1173 1586 1587 695 1737 1588 141 1352 148 1477 1756 1478 129 1064 1289 0\n1918 140 154 -48 0 1780 184 1579 987 138 137 1895 1915 1687 1702 1709 1720 504 1065 516 523 1722 1728 515 1916 1277 1917 1459 104 510 1283 1695 533 1549 352 766 1648 1664 335 988 1064 986 342 1378 422 84 333 1408 0\n1919 -140 -214 0 1561 1111 1529 1579 46 1538 155 1557 1562 1572 1574 1595 226 1593 1594 165 170 173 169 171 172 1752 1732 1569 177 0\n1920 -184 -178 -214 0 1569 177 1568 171 1561 1111 1529 1579 1562 1572 1573 1574 1595 226 1594 165 166 170 173 169 172 1732 0\n1921 145 147 57 -161 270 106 117 -420 -81 -32 391 34 -48 0 1780 168 1604 184 1605 138 1362 1879 1542 937 1393 942 522 464 1708 863 0\n1922 -145 76 298 17 107 0 504 516 1701 574 533 501 1549 1548 761 0\n1923 202 34 29 33 28 -178 -48 0 1780 1731 107 184 1561 1111 1529 1569 177 939 1920 155 1605 293 185 1568 171 1579 1919 1918 525 1685 844 1664 352 1712 497 65 1571 1051 138 137 172 1022 1732 78 80 82 1356 1358 923 926 928 1630 1024 858 1021 1705 1706 495 496 921 1508 1404 1545 1050 531 1268 1052 1681 1717 1662 499 492 836 351 864 1620 1547 1686 1277 1335 1616 305 1922 1362 1921 937 737 1361 1354 743 917 1353 0\n1924 -161 10 25 18 -32 391 34 -178 -48 0 1780 168 1589 1343 1645 107 184 1920 155 1556 1599 895 1569 887 1579 1919 1918 525 1685 844 1664 352 1712 1561 1111 1529 1605 1571 138 137 71 532 1277 1686 1718 1922 1335 840 1362 1616 1626 937 305 897 861 942 1361 894 1711 1618 430 901 1048 307 868 1542 1723 569 893 522 1334 886 1552 1627 889 749 710 350 1619 1545 1046 706 1042 1400 0\n1925 -392 426 88 50 104 0 942 1361 1649 1289 1036 1396 1033 0\n1926 34 29 199 33 28 -178 -48 0 1780 184 1920 155 1605 293 904 185 1569 177 1579 1919 1918 525 1685 844 1664 352 1561 1111 1529 138 137 939 1731 107 168 301 1097 1923 1576 1581 1594 156 162 149 1924 1349 903 906 1348 1632 1278 322 1335 1669 1687 488 534 1040 1925 937 946 1362 1673 1701 123 490 1671 533 489 1549 1426 761 1096 1548 1100 501 1666 573 851 0\n1927 -377 330 -34 -48 0 170 1591 1034 1040 1033 534 187 1288 184 1579 1919 1918 525 1685 844 1664 352 1712 497 65 1571 1051 1561 906 1348 1638 1662 747 328 1052 1050 1404 40 495 735 1398 622 100 350 510 1661 1672 836 551 0\n1928 330 -34 376 -48 0 170 1591 1034 1288 119 184 1579 1919 1918 525 1685 844 1664 352 1712 65 1040 1033 1927 903 908 1349 635 71 495 1037 350 1543 1627 569 1334 0\n1929 -34 415 -178 -48 0 1556 1599 895 184 1605 293 904 1579 1919 1918 525 1685 844 1664 352 1571 138 119 170 1567 918 1928 1687 1709 1719 1720 1721 504 1335 523 1718 1722 509 1632 840 515 906 1626 1821 903 897 1354 1349 894 917 1277 901 921 32 1706 518 615 522 1457 510 1283 1695 1549 533 0\n1930 -29 194 -178 -48 0 184 1919 1918 525 1712 1561 1111 1529 1605 45 166 1746 1355 1588 921 495 217 1678 1706 1676 1343 853 615 1337 1645 1652 1640 1641 414 522 398 305 306 308 1552 307 341 1501 1667 1545 868 350 569 1627 1334 0\n1931 33 194 -178 -48 0 1930 1003 1929 165 184 1605 293 904 1569 177 1568 171 1919 1918 525 1712 1561 1111 1529 1571 939 1926 1731 1923 1590 214 168 1284 1576 1581 250 149 1589 156 162 1588 174 1924 148 1349 903 906 1632 1335 1687 1891 326 847 1550 555 1282 495 1732 1546 731 0\n1932 194 -178 -48 0 184 1920 155 1556 1599 178 1569 887 1919 1918 525 1712 497 1561 1111 1529 1605 1191 1571 1003 1931 169 1751 1612 921 1678 1706 1017 853 615 1002 1624 1640 1641 522 305 306 1552 341 786 1667 355 1194 868 1190 569 1334 1627 386 350 867 1545 1710 531 1865 856 1717 491 1619 1866 308 1626 1501 343 15 1876 1390 0\n1933 -33 -178 -48 0 1780 1556 1932 1587 201 1343 1645 333 1551 184 1605 288 299 1920 155 1599 178 1569 887 177 1568 1919 1918 525 1712 497 1561 1111 1529 1191 144 1571 111 169 1751 199 921 974 1706 559 615 522 1552 341 786 1667 355 1194 868 1190 569 606 1334 516 1627 350 1545 531 720 1865 1717 491 492 1866 1626 1662 343 1856 28 704 1371 1870 973 1625 976 857 1704 0\n1934 151 -178 -48 0 1780 1933 1932 1586 1588 148 184 1605 1556 288 299 1599 283 1920 155 178 1569 887 177 1568 171 293 1919 1918 525 1712 497 1685 503 1276 1561 1111 1529 1191 1571 1552 341 786 1653 1667 863 1194 868 1708 1190 569 1334 1627 350 1545 531 1725 1865 1717 491 836 1866 1620 1662 864 1686 1335 459 345 1872 1204 508 1282 555 542 495 1890 1546 1386 1280 731 1929 1732 0\n1935 -178 -48 0 1780 184 1579 987 1919 1918 525 1685 991 986 1276 64 137 1556 1599 1932 1566 1587 283 201 1182 1343 1645 1652 333 1551 1934 127 522 777 1708 1188 863 623 1181 407 838 327 1624 990 334 1646 1647 423 345 346 343 1186 0\n1936 -268 -151 -48 0 1780 184 1919 1918 525 1712 497 65 522 1708 623 1508 1545 531 1681 1334 1627 1571 1051 1707 622 495 496 1404 1050 1052 1662 351 1626 343 1935 1563 1685 576 843 1657 345 1605 1191 1723 1198 1190 1188 787 1579 844 1664 352 1631 64 137 1659 462 461 333 330 329 1551 1490 168 777 103 353 1604 480 1182 323 1181 1486 0\n1937 -108 260 -455 69 100 93 104 0 103 353 1649 448 335 342 1445 0\n1938 -151 -48 0 1780 1935 1563 184 1579 1919 1918 525 1685 844 1664 352 1712 497 65 1605 1191 1571 1051 137 522 787 1707 1708 1723 576 622 528 623 1198 868 843 495 496 921 1508 1190 486 1657 1404 1751 1545 338 345 1050 531 1268 1052 1681 1662 1136 351 1730 1936 347 863 1604 168 660 333 778 1645 1937 1195 354 783 1666 109 334 0\n1939 -116 -48 0 184 1919 1918 525 1712 1605 1561 1111 1529 1938 1552 341 1667 868 569 1334 1627 350 1545 531 1717 492 720 1935 839 1625 441 343 144 491 714 1711 28 524 0\n1940 -415 33 260 -48 0 1780 1343 1589 168 660 1876 1285 1173 1737 184 1605 1191 1561 1111 1529 1938 1552 341 1667 1194 1190 1919 1918 525 1712 868 569 1334 1627 350 1545 531 786 497 1935 839 473 1939 1856 1717 1120 1110 720 189 1579 157 1571 151 1003 1384 1586 1271 1588 1432 148 22 717 1473 0\n1941 -60 36 -442 37 -48 0 184 1919 1918 525 1712 1605 1561 1111 1529 1938 1552 341 1667 868 569 1334 1627 350 1545 22 717 1085 0\n1942 36 -254 129 -48 0 1780 1644 1087 184 1561 1111 1529 1938 1552 786 1919 1918 525 1712 497 1605 1191 341 1667 1194 1190 1939 1204 508 1694 1089 1084 1282 519 1903 1645 1343 1589 168 660 1876 868 569 1334 1627 350 1545 531 1871 1861 178 1599 143 1935 1563 924 1358 923 926 1630 337 839 473 1856 1625 336 150 50 1264 1941 1501 19 690 0\n1943 -254 129 -48 0 1780 184 1561 1111 1529 1938 1552 786 1919 1918 525 1712 497 1605 1191 341 1667 1194 1190 1939 1204 96 868 569 1334 1627 350 1545 531 1871 983 1935 978 977 138 1645 1343 1589 168 660 1876 1861 30 1942 52 1373 313 1262 1624 1391 1008 1002 742 1940 0\n1944 59 100 -48 0 1780 184 1561 1111 1529 1938 1552 786 1919 1918 525 1712 1605 341 1667 868 569 1334 1627 350 1545 1725 1276 1685 503 1872 497 1191 1194 1190 1939 1204 1282 96 983 1935 978 977 1943 333 1374 52 508 1694 1089 531 839 473 1856 351 1579 844 1664 352 64 1563 924 1358 923 926 1630 337 928 83 1416 1084 1941 555 495 1717 1120 1110 720 1501 1433 9 775 1495 0\n1945 100 -48 0 1780 184 1605 1191 1561 1111 1529 1938 1552 341 1667 1194 1190 1919 1918 525 1712 868 569 1334 1627 350 1545 531 786 497 1935 839 473 1939 1856 1871 1717 1120 1110 720 1725 351 1716 1625 441 343 355 1653 983 978 977 1563 924 1579 1685 844 1664 352 503 1276 65 64 137 1872 1358 923 926 1630 337 1204 96 508 1282 773 1694 1089 1714 1943 1095 333 417 1551 1374 928 330 168 52 83 1604 1416 863 1084 630 1941 1944 15 307 1878 1390 1618 1002 852 1003 1591 1586 1587 187 1588 141 148 1418 1090 1093 1094 1647 99 334 1434 0\n1946 -48 0 184 1561 1579 1111 987 1529 1919 1918 525 1276 1685 991 986 1938 1552 341 1653 1945 345 1637 1657 457 327 402 320 319 326 1377 0\n1947 59 0 1946 1852 0\n1948 -3 0 1947 12 0\n1949 -28 0 1947 14 0\n1950 -84 0 1947 15 0\n1951 -115 0 1947 16 0\n1952 -139 0 1947 17 0\n1953 225 0 1947 307 0\n1954 -256 0 1953 1618 0\n1955 -257 0 1953 1650 0\n1956 -90 0 1954 335 0\n1957 -392 0 1954 942 0\n1958 -91 0 1955 336 0\n1959 -395 0 1955 953 0\n1960 -125 0 68 70 72 1347 1348 1349 903 0\n1961 -88 -151 159 0 1947 1955 1946 1957 1954 1780 1951 1949 1553 349 1620 1319 1726 1545 531 1717 836 1606 1660 522 1723 868 303 857 1703 489 126 1561 1681 708 1305 107 333 1520 1360 484 1604 285 937 1100 852 1362 1693 1701 1702 561 123 557 533 632 534 496 921 495 488 1427 1746 1096 1747 1097 169 1612 0\n1962 -33 -145 -151 159 0 1959 1946 1780 1947 1958 1955 1961 1551 168 1589 1343 438 1337 1688 488 516 123 1553 1319 1726 1545 531 603 1754 122 323 1163 1737 699 1284 349 1620 1717 836 1606 1660 522 1723 868 303 950 949 1708 528 1707 527 127 1681 1334 169 704 1612 959 1097 133 1096 1100 1654 434 337 1174 85 338 758 1651 435 437 319 316 1060 1424 1728 1278 1409 0\n1963 -37 17 53 88 -469 54 96 -104 0 1780 1958 1551 168 1589 1163 1737 1284 1319 1726 349 1660 78 80 81 82 173 1356 1358 1582 923 162 926 928 1489 1630 478 326 67 337 352 481 1479 353 0\n1964 -41 146 35 116 -160 0 1958 177 717 1560 19 143 0\n1965 -151 159 0 1954 1955 1957 1780 1947 1946 1949 1553 349 1620 1319 1726 1545 531 1717 836 1606 1681 708 426 334 1660 1194 126 127 522 788 1708 1723 549 528 1198 868 491 1190 303 171 1961 1551 168 699 777 1589 1604 1343 182 438 323 1964 941 937 946 1362 120 1962 109 705 1536 155 1792 1963 1732 561 1746 921 0\n1966 40 33 159 0 1954 1946 1955 1780 1947 1958 1965 1553 349 1620 1319 1726 1545 531 1717 836 1606 492 718 426 882 309 1305 1552 881 341 1304 879 1653 441 365 1303 884 885 468 343 308 1551 1722 705 867 28 168 699 301 524 710 303 1711 171 491 19 0\n1967 35 -40 159 0 1954 1950 1958 1949 1959 1947 1946 1957 1780 176 1596 1553 1319 1726 1545 718 349 1620 1116 531 1717 1120 1110 1535 178 1536 155 1660 1194 1613 1191 1190 426 334 125 1389 785 1965 708 1364 1386 949 1002 957 1017 1679 1696 497 488 1873 699 958 130 523 941 1674 937 491 1362 1871 0\n1968 -428 -32 60 96 -235 0 1954 1958 168 1589 1163 1737 1284 107 418 330 1614 1046 1619 364 342 337 1174 83 338 1401 1635 326 0\n1969 -32 -40 159 0 1946 1948 1955 1780 1952 1967 171 1580 162 1575 156 176 1596 1553 1319 1726 1545 718 349 1620 1116 531 1717 1120 1110 1535 178 1536 155 1568 150 20 1592 1594 149 1400 25 24 22 1538 125 1965 1681 1334 168 1589 1343 261 438 148 1337 1069 1676 1688 1729 495 488 1546 1260 1968 1042 1048 1402 1674 489 523 1671 1672 543 1673 546 510 509 516 515 1073 0\n1970 33 159 0 1954 1958 1950 1949 1947 1946 1553 349 1620 1116 1319 1726 1545 531 1717 1120 1110 718 426 334 1966 125 176 1389 1596 1613 1535 189 178 1536 155 1969 1384 1873 1002 488 1017 1696 0\n1971 -40 159 0 1946 1947 1780 1953 1970 704 1553 349 1620 1116 1319 1726 1545 531 1717 1120 1110 492 718 309 176 1969 1535 660 178 333 28 1659 343 452 0\n1972 159 0 1946 1947 1955 1780 1956 1553 349 1305 1319 1620 1726 309 1545 531 708 718 1717 492 1965 1970 169 782 704 1612 188 1971 1552 341 1304 1653 441 365 1303 468 343 1551 354 28 168 116 178 1604 516 1599 863 603 835 1715 597 0\n1973 -104 0 1972 139 0\n1974 326 0 1972 530 0\n1975 356 0 1972 1324 0\n1976 -283 0 1974 1675 0\n1977 -332 0 1974 1716 0\n1978 -160 0 1975 1727 0\n1979 -453 0 1976 1120 0\n1980 105 0 1978 1545 0\n1981 271 0 1980 350 0\n1982 -346 0 1980 1310 0\n1983 -235 0 1981 1627 0\n1984 -227 0 1981 1661 0\n1985 -263 0 1981 1955 446 0\n1986 -345 0 1982 1972 1309 0\n1987 291 0 1983 1334 0\n1988 -455 0 1983 1123 0\n1989 -452 0 1984 1116 0\n1990 -255 0 1984 1953 362 0\n1991 172 0 1984 1976 836 0\n1992 -97 0 1985 342 0\n1993 -278 0 1987 1668 0\n1994 456 0 1988 1730 0\n1995 451 0 1989 1979 1110 0\n1996 -89 0 1990 334 0\n1997 -215 0 1991 1606 0\n1998 -280 0 1993 1670 0\n1999 -42 0 1995 1980 1541 0\n2000 -114 0 1998 489 0\n2001 -373 0 1999 1346 0\n2002 -140 0 1999 1980 1946 1540 0\n2003 -124 0 2001 1973 1521 0\n2004 -147 0 2003 1980 1539 0\n2005 -289 0 2004 1977 2002 1805 0\n2006 -123 0 2005 497 0\n2007 288 0 2006 2003 1980 1508 0\n2008 -306 0 2007 1678 0\n2009 -417 0 2008 1017 0\n2010 -32 0 1950 1996 1956 2009 1999 1949 1955 1997 1977 2006 2003 1994 1960 2000 1958 1992 107 168 1284 1009 1589 1002 174 1343 1163 1003 1386 438 1737 1586 1587 171 1337 1588 141 1580 303 1676 148 162 868 495 1667 1546 1446 341 1829 738 690 1174 1550 338 326 1635 0\n2011 88 0 2010 1780 660 0\n2012 254 0 2011 333 0\n2013 344 0 2011 1306 0\n2014 -260 0 2012 1645 0\n2015 -96 0 2013 1986 1307 0\n2016 204 0 2014 1343 0\n2017 -416 0 2015 1958 1992 1996 1950 1956 1010 0\n2018 -198 0 2016 1589 0\n2019 415 0 2017 2009 1002 0\n2020 34 0 2019 1999 1946 2010 1949 1383 0\n2021 54 0 2019 1999 1949 2010 1385 0\n2022 200 0 2020 170 0\n2023 220 0 2021 189 0\n2024 0 2022 2023 2018 257 0\n"

theorem raw_n8_b7_p0012 (word:Fin 8→Fin 3) (base val:Sat.Valuation)
 (h:ModuleOPG1808CNF.LexModel word (lexRot 8) lexPerm base)
 (heq:∀ i,i<OPG1808Cuts.selectorBase 8→(val i↔base i))
 (hc:OPG1808Cuts.CutModel (n:=8) 7 val)
 (hp:word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(2:Fin 3)∧True):False:=by
 have m:=h.toModel
 have bad:=cert_n8_b7_p0012 (val 1) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 145) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 266) (val 267) (val 268) (val 269) (val 270) (val 271) (val 272) (val 273) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 336) (val 337) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 524) (val 525) (val 526) (val 527) (val 538) (val 539) (val 540) (val 541) (val 559) (val 560) (val 573) (val 574) (val 575) (val 587) (val 588) (val 589) (val 594) (val 595) (val 596) (val 643) (val 644) (val 645) (val 650) (val 651) (val 652) (val 671) (val 672) (val 716) (val 717) (val 718) (val 722) (val 723) (val 724) (val 725) (val 726) (val 727) (val 728) (val 729) (val 730) (val 731) (val 732) (val 733) (val 734) (val 735) (val 736) (val 737) (val 738) (val 739) (val 740) (val 741) (val 742) (val 743) (val 744) (val 745) (val 746) (val 747) (val 748) (val 749) (val 750) (val 751) (val 752) (val 753) (val 754) (val 755) (val 756) (val 757) (val 758) (val 759) (val 760) (val 761) (val 762) (val 763) (val 764) (val 765) (val 766) (val 767) (val 768) (val 769) (val 770) (val 771) (val 772) (val 773) (val 774) (val 775) (val 776) (val 777) (val 778) (val 779) (val 780) (val 781) (val 782) (val 783) (val 784) (val 785) (val 786) (val 787) (val 788) (val 789) (val 790) (val 791) (val 792) (val 793) (val 794) (val 795) (val 796) (val 797) (val 798) (val 799) (val 800) (val 801) (val 802) (val 803) (val 804) (val 805) (val 806) (val 807) (val 808) (val 809) (val 810) (val 811) (val 812) (val 813) (val 814) (val 818) (val 819) (val 820) (val 821) (val 822) (val 823) (val 824) (val 825) (val 826) (val 827) (val 828) (val 829) (val 830) (val 831) (val 832)
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
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 0 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 0 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 0 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 3 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 0 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 4 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 4 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 0 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 5 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 3 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 4 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 4 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 1 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 1 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 1 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 6 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 5 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 4 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 5 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 3 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 3 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 6 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 4 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 5 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 5 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 5 7 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 6 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 7 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 1) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 5) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 1) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 0) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 5) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 1) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 7) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 3) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 7) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 3) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 4) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 7) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 5) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 2) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 2) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 2) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 6) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 5) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 5) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 4) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 7) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 4) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 7) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 2) (by decide)) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 7) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 7) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 0) (by decide)) (b))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 0) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 0) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 1) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 1) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 2) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 2) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 2) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 3) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 3) (by decide)) (b)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 3) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 4) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 5) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 5) (by decide)) (b))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 6) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 6) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 6) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 0 (hp.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 1 (hp.2.1)) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 1 2 (hp.2.2.1)) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 2 3 (hp.2.2.2.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 20 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 20 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 20 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 1 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 20 2 2 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 2 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 3 1 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 20 3 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 22 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 22 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 22 1 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 22 2 2 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 22 2 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 22 2 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 22 3 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 22 3 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 25 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 25 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 25 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 27 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 27 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 1 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 27 1 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 27 2 2 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 29 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 29 1 1 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 29 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 30 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 30 1 1 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 30 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 37 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 37 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 37 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 38 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 38 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 38 1 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 38 2 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 41 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 1 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 0 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 1 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 1 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 3 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 3 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 6 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 1 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 1 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 1 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 3 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 4) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 4 2) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 6 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 7) (b.1) (b.2.1) (b.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 0 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 0 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 1 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 1 2) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 2) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 4 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 5) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 6 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 6 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 2 (by decide) 0) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 0 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 0 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 0 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 1 0) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 1 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 2 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 3) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 0 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 0 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 4 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 5 1) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 0) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 0 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 1 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 2 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 3 2) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 4) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 4 2) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 5 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 6) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 7) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 7 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 1 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 3) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 17) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 21) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 3 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 0 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 25) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 26) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 1) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 7 1) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 19) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 21) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))))))))
end OPG1808CutCertificates
end

end Cut8Prefix0012CompactV3Packet

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
    (hprefix3 : color (3:Fin 8) (finRotate 8 (3:Fin 8)) = (2:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  exact Cut8Prefix0012CompactV3Packet.OPG1808PhysicalPrefix.predecessor_reachable_of_cut_exclusion
    (fun word ↦ word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(1:Fin 3)∧word (3:Fin 8)=(2:Fin 3)∧True) Cut8Prefix0012CompactV3Packet.OPG1808CutCertificates.raw_n8_b7_p0012
    D color htournament hnoRainbow hcycle hminimal ⟨hprefix0,hprefix1,hprefix2,hprefix3,True.intro⟩
