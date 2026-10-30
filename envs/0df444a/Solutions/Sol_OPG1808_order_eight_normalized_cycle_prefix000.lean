-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix000
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:27:55.434049+00:00
-- url     : https://prove2.me/submissions/a6431738-64b4-415f-9c4d-560f715e87d8

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

namespace Cut8Prefix000Packet

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
lrat_proof cert_n8_b7_p000
 "p cnf 833 1441\n-2 -66 0\n-2 -130 0\n-67 -131 0\n4 25 68 89 132 153 0\n-68 -132 0\n5 33 69 97 133 161 0\n-69 -97 0\n-69 -133 0\n-69 -161 0\n6 41 70 105 134 169 0\n-6 -41 0\n-41 -70 0\n-41 -169 0\n-105 -134 0\n-134 -169 0\n7 49 71 113 135 177 0\n-7 -49 0\n-49 -135 0\n-49 -177 0\n-71 -177 0\n-113 -135 0\n-135 -177 0\n8 57 72 121 136 185 0\n-57 -121 0\n-57 -185 0\n-121 -185 0\n-11 -75 0\n-11 -139 0\n13 34 77 98 141 162 0\n-13 -77 0\n-13 -98 0\n-13 -141 0\n-13 -162 0\n-77 -98 0\n-98 -141 0\n-141 -162 0\n14 42 78 106 142 170 0\n-14 -106 0\n-14 -170 0\n-42 -170 0\n-78 -106 0\n-78 -170 0\n-106 -142 0\n-106 -170 0\n-142 -170 0\n15 50 79 114 143 178 0\n-15 -50 0\n-15 -114 0\n-15 -178 0\n-50 -114 0\n-50 -178 0\n-79 -114 0\n-79 -178 0\n-114 -143 0\n-114 -178 0\n-143 -178 0\n16 58 80 122 144 186 0\n-58 -80 0\n-58 -122 0\n-58 -144 0\n-58 -186 0\n-80 -122 0\n-80 -186 0\n-122 -144 0\n-122 -186 0\n-144 -186 0\n-20 -84 0\n-20 -148 0\n21 35 85 99 149 163 0\n-21 -85 0\n-21 -149 0\n-85 -149 0\n-99 -149 0\n-149 -163 0\n22 43 86 107 150 171 0\n-22 -43 0\n-22 -86 0\n-43 -86 0\n-86 -107 0\n-86 -150 0\n-86 -171 0\n-107 -150 0\n-150 -171 0\n23 51 87 115 151 179 0\n-23 -51 0\n-23 -87 0\n-23 -151 0\n-23 -179 0\n-51 -87 0\n-51 -151 0\n-51 -179 0\n-87 -115 0\n-87 -151 0\n-87 -179 0\n-115 -151 0\n-151 -179 0\n24 59 88 123 152 187 0\n-59 -123 0\n-59 -187 0\n-88 -123 0\n-88 -187 0\n-123 -152 0\n-123 -187 0\n-152 -187 0\n29 36 93 100 157 164 0\n-29 -93 0\n30 44 94 108 158 172 0\n-30 -44 0\n-30 -94 0\n-30 -108 0\n-30 -158 0\n-44 -94 0\n-44 -158 0\n-94 -108 0\n-94 -158 0\n-94 -172 0\n-108 -158 0\n-158 -172 0\n31 52 95 116 159 180 0\n-31 -52 0\n-31 -159 0\n-31 -180 0\n-52 -95 0\n-52 -159 0\n-95 -116 0\n-95 -159 0\n-95 -180 0\n-159 -180 0\n32 60 96 124 160 188 0\n-96 -124 0\n-96 -160 0\n-96 -188 0\n-124 -160 0\n-124 -188 0\n-160 -188 0\n38 45 102 109 166 173 0\n-38 -102 0\n-38 -166 0\n-102 -166 0\n39 53 103 117 167 181 0\n-39 -53 0\n-39 -103 0\n-39 -167 0\n-39 -181 0\n-53 -103 0\n-53 -167 0\n-103 -117 0\n-103 -167 0\n-103 -181 0\n-117 -167 0\n-167 -181 0\n40 61 104 125 168 189 0\n-40 -61 0\n-61 -104 0\n-61 -168 0\n-104 -125 0\n-104 -168 0\n-125 -168 0\n-168 -189 0\n47 54 111 118 175 182 0\n-47 -111 0\n-47 -175 0\n-111 -175 0\n-48 -62 0\n-48 -112 0\n-48 -176 0\n-62 -112 0\n-62 -176 0\n-112 -126 0\n-112 -176 0\n-126 -176 0\n-176 -190 0\n56 63 120 127 184 191 0\n-56 -120 0\n-56 -184 0\n-120 -184 0\n-2 194 0\n-5 197 0\n-6 198 0\n-7 199 0\n-8 200 0\n-9 201 0\n-11 203 0\n-13 205 0\n-14 206 0\n-15 207 0\n-16 208 0\n-17 209 0\n-18 210 0\n-20 212 0\n-21 213 0\n-22 214 0\n-23 215 0\n-24 216 0\n-25 217 0\n-26 218 0\n-27 219 0\n-29 221 0\n-30 222 0\n-31 223 0\n-32 224 0\n-33 225 0\n-34 226 0\n-35 227 0\n-36 228 0\n-38 230 0\n-39 231 0\n-40 232 0\n-41 233 0\n-42 234 0\n-43 235 0\n-44 236 0\n-45 237 0\n-47 239 0\n-48 240 0\n-49 241 0\n-50 242 0\n-51 243 0\n-52 244 0\n-53 245 0\n-54 246 0\n-56 248 0\n-57 249 0\n-58 250 0\n-59 251 0\n-60 252 0\n-61 253 0\n-63 255 0\n-194 -203 195 0\n-194 -205 197 0\n-194 -208 200 0\n-195 -212 196 0\n-195 -213 197 0\n-195 -214 198 0\n-196 -221 197 0\n-196 -222 198 0\n-198 -240 200 0\n-199 -248 200 0\n-203 -212 204 0\n-203 -213 205 0\n-203 -214 206 0\n-203 -215 207 0\n-203 -216 208 0\n-204 -221 205 0\n-204 -222 206 0\n-204 -223 207 0\n-205 -230 206 0\n-205 -231 207 0\n-205 -232 208 0\n-206 -233 201 0\n-206 -239 207 0\n-206 -240 208 0\n-207 -241 201 0\n-207 -245 205 0\n-207 -248 208 0\n-209 -194 210 0\n-212 -221 213 0\n-212 -222 214 0\n-212 -223 215 0\n-212 -224 216 0\n-213 -230 214 0\n-213 -231 215 0\n-213 -232 216 0\n-214 -233 209 0\n-214 -234 210 0\n-214 -239 215 0\n-214 -240 216 0\n-215 -241 209 0\n-215 -242 210 0\n-215 -248 216 0\n-217 -195 219 0\n-218 -203 219 0\n-221 -230 222 0\n-221 -231 223 0\n-221 -232 224 0\n-222 -233 217 0\n-222 -234 218 0\n-222 -235 219 0\n-222 -239 223 0\n-222 -240 224 0\n-223 -241 217 0\n-223 -242 218 0\n-223 -243 219 0\n-223 -245 221 0\n-223 -248 224 0\n-225 -196 228 0\n-226 -204 228 0\n-227 -212 228 0\n-230 -234 226 0\n-230 -235 227 0\n-230 -236 228 0\n-230 -239 231 0\n-230 -240 232 0\n-231 -241 225 0\n-231 -242 226 0\n-231 -243 227 0\n-231 -244 228 0\n-232 -250 226 0\n-233 -194 234 0\n-233 -197 237 0\n-234 -203 235 0\n-234 -205 237 0\n-235 -212 236 0\n-235 -213 237 0\n-235 -215 239 0\n-236 -221 237 0\n-236 -223 239 0\n-239 -241 233 0\n-239 -242 234 0\n-239 -244 236 0\n-239 -245 237 0\n-239 -248 240 0\n-240 -249 233 0\n-240 -250 234 0\n-240 -251 235 0\n-240 -252 236 0\n-240 -253 237 0\n-241 -194 242 0\n-241 -195 243 0\n-241 -196 244 0\n-241 -197 245 0\n-241 -198 246 0\n-242 -203 243 0\n-242 -204 244 0\n-242 -205 245 0\n-242 -206 246 0\n-243 -212 244 0\n-243 -213 245 0\n-243 -214 246 0\n-244 -221 245 0\n-244 -222 246 0\n-245 -230 246 0\n-248 -250 242 0\n-248 -251 243 0\n-248 -252 244 0\n-248 -253 245 0\n-248 -254 246 0\n-249 -197 253 0\n-250 -203 251 0\n-250 -204 252 0\n-250 -205 253 0\n-250 -207 255 0\n-251 -212 252 0\n-251 -213 253 0\n-251 -215 255 0\n-252 -221 253 0\n-252 -223 255 0\n-253 -231 255 0\n-254 -239 255 0\n-67 259 0\n-68 260 0\n-69 261 0\n-70 262 0\n-71 263 0\n-72 264 0\n-73 265 0\n-76 268 0\n-77 269 0\n-78 270 0\n-79 271 0\n-80 272 0\n-82 274 0\n-85 277 0\n-86 278 0\n-87 279 0\n-88 280 0\n-89 281 0\n-91 283 0\n-93 285 0\n-94 286 0\n-95 287 0\n-96 288 0\n-97 289 0\n-98 290 0\n-99 291 0\n-100 292 0\n-102 294 0\n-103 295 0\n-104 296 0\n-105 297 0\n-106 298 0\n-107 299 0\n-108 300 0\n-109 301 0\n-111 303 0\n-112 304 0\n-113 305 0\n-114 306 0\n-115 307 0\n-116 308 0\n-117 309 0\n-118 310 0\n-120 312 0\n-121 313 0\n-122 314 0\n-123 315 0\n-124 316 0\n-125 317 0\n-126 318 0\n-127 319 0\n-258 -272 264 0\n-259 -277 261 0\n-259 -280 264 0\n-260 -285 261 0\n-260 -286 262 0\n-260 -288 264 0\n-261 -290 258 0\n-261 -291 259 0\n-261 -294 262 0\n-261 -295 263 0\n-261 -296 264 0\n-262 -298 258 0\n-262 -303 263 0\n-262 -304 264 0\n-263 -306 258 0\n-263 -312 264 0\n-268 -281 265 0\n-268 -288 272 0\n-269 -289 265 0\n-269 -294 270 0\n-269 -295 271 0\n-269 -296 272 0\n-270 -297 265 0\n-270 -299 267 0\n-270 -303 271 0\n-270 -304 272 0\n-271 -305 265 0\n-272 -313 265 0\n-272 -315 267 0\n-272 -317 269 0\n-273 -258 274 0\n-273 -261 277 0\n-273 -262 278 0\n-276 -285 277 0\n-277 -290 274 0\n-277 -294 278 0\n-277 -295 279 0\n-277 -296 280 0\n-278 -298 274 0\n-278 -303 279 0\n-278 -304 280 0\n-279 -306 274 0\n-279 -308 276 0\n-279 -309 277 0\n-279 -312 280 0\n-280 -314 274 0\n-280 -316 276 0\n-280 -317 277 0\n-280 -318 278 0\n-281 -259 283 0\n-281 -262 286 0\n-282 -270 286 0\n-285 -291 283 0\n-285 -294 286 0\n-285 -295 287 0\n-286 -297 281 0\n-286 -299 283 0\n-286 -303 287 0\n-286 -304 288 0\n-287 -305 281 0\n-287 -307 283 0\n-287 -312 288 0\n-288 -315 283 0\n-288 -317 285 0\n-289 -259 291 0\n-289 -260 292 0\n-290 -267 291 0\n-290 -268 292 0\n-290 -270 294 0\n-290 -271 295 0\n-294 -297 289 0\n-294 -298 290 0\n-294 -299 291 0\n-294 -300 292 0\n-294 -303 295 0\n-294 -304 296 0\n-295 -305 289 0\n-295 -306 290 0\n-295 -307 291 0\n-295 -308 292 0\n-295 -312 296 0\n-296 -313 289 0\n-296 -314 290 0\n-296 -315 291 0\n-296 -316 292 0\n-297 -261 301 0\n-298 -268 300 0\n-298 -269 301 0\n-298 -271 303 0\n-299 -276 300 0\n-299 -277 301 0\n-299 -279 303 0\n-299 -280 304 0\n-300 -285 301 0\n-303 -306 298 0\n-303 -307 299 0\n-303 -308 300 0\n-303 -309 301 0\n-303 -312 304 0\n-304 -313 297 0\n-304 -314 298 0\n-304 -315 299 0\n-304 -316 300 0\n-304 -317 301 0\n-305 -259 307 0\n-305 -262 310 0\n-306 -268 308 0\n-306 -269 309 0\n-306 -270 310 0\n-307 -277 309 0\n-307 -278 310 0\n-308 -281 305 0\n-308 -282 306 0\n-308 -285 309 0\n-308 -286 310 0\n-308 -288 312 0\n-309 -290 306 0\n-309 -294 310 0\n-312 -313 305 0\n-312 -314 306 0\n-312 -315 307 0\n-312 -316 308 0\n-312 -317 309 0\n-312 -318 310 0\n-313 -259 315 0\n-313 -260 316 0\n-313 -261 317 0\n-313 -262 318 0\n-313 -263 319 0\n-314 -267 315 0\n-314 -268 316 0\n-314 -269 317 0\n-314 -270 318 0\n-314 -271 319 0\n-315 -277 317 0\n-315 -278 318 0\n-315 -279 319 0\n-316 -282 314 0\n-316 -285 317 0\n-316 -286 318 0\n-316 -287 319 0\n-317 -289 313 0\n-317 -290 314 0\n-317 -291 315 0\n-317 -294 318 0\n-317 -295 319 0\n-318 -298 314 0\n-318 -299 315 0\n-318 -303 319 0\n-131 323 0\n-132 324 0\n-133 325 0\n-134 326 0\n-135 327 0\n-136 328 0\n-137 329 0\n-140 332 0\n-141 333 0\n-142 334 0\n-143 335 0\n-145 337 0\n-146 338 0\n-149 341 0\n-150 342 0\n-151 343 0\n-152 344 0\n-153 345 0\n-154 346 0\n-155 347 0\n-158 350 0\n-159 351 0\n-160 352 0\n-161 353 0\n-162 354 0\n-163 355 0\n-164 356 0\n-166 358 0\n-167 359 0\n-168 360 0\n-169 361 0\n-170 362 0\n-171 363 0\n-172 364 0\n-173 365 0\n-175 367 0\n-176 368 0\n-177 369 0\n-178 370 0\n-179 371 0\n-180 372 0\n-181 373 0\n-182 374 0\n-184 376 0\n-185 377 0\n-186 378 0\n-187 379 0\n-188 380 0\n-189 381 0\n-190 382 0\n-191 383 0\n-322 -333 325 0\n-322 -336 328 0\n-323 -342 326 0\n-323 -343 327 0\n-323 -344 328 0\n-324 -350 326 0\n-324 -351 327 0\n-324 -352 328 0\n-325 -354 322 0\n-325 -355 323 0\n-325 -358 326 0\n-325 -359 327 0\n-325 -360 328 0\n-326 -362 322 0\n-326 -364 324 0\n-326 -367 327 0\n-326 -368 328 0\n-327 -370 322 0\n-327 -371 323 0\n-327 -372 324 0\n-327 -373 325 0\n-327 -376 328 0\n-331 -337 329 0\n-331 -342 334 0\n-332 -345 329 0\n-332 -350 334 0\n-332 -351 335 0\n-332 -352 336 0\n-333 -353 329 0\n-333 -355 331 0\n-333 -358 334 0\n-333 -359 335 0\n-333 -360 336 0\n-334 -361 329 0\n-334 -364 332 0\n-334 -367 335 0\n-334 -368 336 0\n-335 -369 329 0\n-335 -372 332 0\n-335 -376 336 0\n-336 -377 329 0\n-336 -379 331 0\n-336 -380 332 0\n-336 -381 333 0\n-336 -382 334 0\n-337 -324 340 0\n-340 -350 342 0\n-341 -353 337 0\n-341 -354 338 0\n-341 -358 342 0\n-341 -359 343 0\n-341 -360 344 0\n-342 -361 337 0\n-342 -362 338 0\n-342 -364 340 0\n-342 -367 343 0\n-342 -368 344 0\n-343 -370 338 0\n-343 -372 340 0\n-343 -373 341 0\n-343 -376 344 0\n-344 -377 337 0\n-344 -378 338 0\n-344 -380 340 0\n-344 -381 341 0\n-344 -382 342 0\n-345 -323 347 0\n-345 -326 350 0\n-346 -333 349 0\n-346 -334 350 0\n-349 -355 347 0\n-350 -363 347 0\n-350 -367 351 0\n-350 -368 352 0\n-351 -370 346 0\n-351 -371 347 0\n-351 -373 349 0\n-351 -376 352 0\n-352 -379 347 0\n-352 -381 349 0\n-353 -324 356 0\n-353 -326 358 0\n-353 -327 359 0\n-354 -332 356 0\n-354 -334 358 0\n-354 -335 359 0\n-354 -336 360 0\n-355 -337 353 0\n-355 -340 356 0\n-355 -342 358 0\n-355 -343 359 0\n-355 -344 360 0\n-358 -361 353 0\n-358 -362 354 0\n-358 -364 356 0\n-358 -367 359 0\n-358 -368 360 0\n-359 -369 353 0\n-359 -370 354 0\n-359 -372 356 0\n-359 -376 360 0\n-360 -377 353 0\n-360 -378 354 0\n-360 -380 356 0\n-360 -382 358 0\n-361 -323 363 0\n-361 -325 365 0\n-361 -327 367 0\n-362 -333 365 0\n-362 -335 367 0\n-362 -336 368 0\n-363 -341 365 0\n-363 -344 368 0\n-364 -345 361 0\n-364 -346 362 0\n-364 -349 365 0\n-367 -370 362 0\n-367 -371 363 0\n-367 -372 364 0\n-367 -373 365 0\n-367 -376 368 0\n-368 -378 362 0\n-368 -379 363 0\n-368 -380 364 0\n-368 -381 365 0\n-369 -323 371 0\n-369 -324 372 0\n-369 -325 373 0\n-369 -326 374 0\n-370 -331 371 0\n-370 -332 372 0\n-370 -333 373 0\n-370 -334 374 0\n-370 -336 376 0\n-371 -341 373 0\n-371 -342 374 0\n-372 -350 374 0\n-373 -354 370 0\n-373 -355 371 0\n-373 -358 374 0\n-373 -360 376 0\n-376 -377 369 0\n-376 -378 370 0\n-376 -379 371 0\n-376 -380 372 0\n-376 -381 373 0\n-376 -382 374 0\n-377 -322 378 0\n-377 -323 379 0\n-377 -324 380 0\n-377 -325 381 0\n-377 -326 382 0\n-377 -327 383 0\n-378 -332 380 0\n-378 -333 381 0\n-378 -334 382 0\n-378 -335 383 0\n-379 -337 377 0\n-379 -341 381 0\n-379 -342 382 0\n-379 -343 383 0\n-380 -346 378 0\n-380 -350 382 0\n-380 -351 383 0\n-381 -353 377 0\n-381 -354 378 0\n-381 -355 379 0\n-381 -358 382 0\n-381 -359 383 0\n-382 -361 377 0\n-382 -362 378 0\n-382 -363 379 0\n-382 -364 380 0\n-382 -367 383 0\n-200 0\n-264 0\n-328 0\n-201 0\n-265 0\n-329 0\n-210 0\n-274 0\n-338 0\n-219 0\n-283 0\n-347 0\n29 93 157 0\n-228 0\n-292 0\n-356 0\n38 102 166 0\n-237 0\n-301 0\n-365 0\n47 111 175 0\n-246 0\n-310 0\n-374 0\n56 120 184 0\n-255 0\n-319 0\n-383 0\n2 0\n11 0\n20 0\n-2 -76 -153 0\n-2 -140 -89 0\n-2 -77 -161 0\n-2 -141 -97 0\n-2 -78 -169 0\n-2 -142 -105 0\n-2 -79 -177 0\n-2 -143 -113 0\n-2 -80 -185 0\n-2 -144 -121 0\n-67 -20 -153 0\n-131 -20 -89 0\n-131 -87 -49 0\n-7 -179 -81 0\n-68 -29 -161 0\n-132 -29 -97 0\n-4 -94 -169 0\n-4 -158 -105 0\n-68 -158 -41 0\n-132 -30 -105 0\n-4 -160 -121 0\n-5 -102 -169 0\n-69 -38 -169 0\n-69 -166 -41 0\n-133 -102 -41 0\n-5 -167 -113 0\n-69 -167 -49 0\n-5 -104 -185 0\n-5 -168 -121 0\n-69 -40 -185 0\n-6 -111 -177 0\n-70 -175 -49 0\n-134 -111 -49 0\n-6 -112 -185 0\n-6 -176 -121 0\n-7 -120 -185 0\n-7 -184 -121 0\n-71 -56 -185 0\n-11 -85 -162 0\n-11 -149 -98 0\n-11 -86 -170 0\n-11 -150 -106 0\n-11 -87 -178 0\n-11 -151 -114 0\n-11 -88 -186 0\n-11 -152 -122 0\n-76 -29 -162 0\n-140 -29 -98 0\n-140 -96 -58 0\n-13 -102 -170 0\n-13 -166 -106 0\n-77 -38 -170 0\n-77 -166 -42 0\n-141 -38 -106 0\n-141 -102 -42 0\n-13 -103 -178 0\n-13 -167 -114 0\n-77 -39 -178 0\n-77 -167 -50 0\n-13 -104 -186 0\n-13 -168 -122 0\n-77 -168 -58 0\n-141 -104 -58 0\n-14 -111 -178 0\n-14 -175 -114 0\n-78 -47 -178 0\n-78 -175 -50 0\n-142 -47 -114 0\n-142 -111 -50 0\n-14 -112 -186 0\n-14 -176 -122 0\n-78 -48 -186 0\n-78 -176 -58 0\n-142 -112 -58 0\n-15 -120 -186 0\n-15 -184 -122 0\n-79 -56 -186 0\n-143 -56 -122 0\n-20 -93 -163 0\n-20 -94 -171 0\n-20 -158 -107 0\n-20 -95 -179 0\n-20 -159 -115 0\n-20 -96 -187 0\n-20 -160 -123 0\n-21 -102 -171 0\n-85 -166 -43 0\n-21 -103 -179 0\n-85 -167 -51 0\n-149 -39 -115 0\n-149 -103 -51 0\n-21 -104 -187 0\n-85 -168 -59 0\n-149 -104 -59 0\n-22 -111 -179 0\n-22 -175 -115 0\n-86 -47 -179 0\n-86 -175 -51 0\n-150 -111 -51 0\n-22 -112 -187 0\n-22 -176 -123 0\n-86 -48 -187 0\n-86 -176 -59 0\n-150 -112 -59 0\n-23 -120 -187 0\n-23 -184 -123 0\n-87 -56 -187 0\n-87 -184 -59 0\n-151 -120 -59 0\n-29 -102 -172 0\n-93 -38 -172 0\n-93 -166 -44 0\n-29 -103 -180 0\n-29 -167 -116 0\n-93 -167 -52 0\n-29 -104 -188 0\n-29 -168 -124 0\n-93 -40 -188 0\n-93 -168 -60 0\n-30 -111 -180 0\n-30 -175 -116 0\n-94 -47 -180 0\n-94 -175 -52 0\n-158 -47 -116 0\n-158 -111 -52 0\n-30 -112 -188 0\n-30 -176 -124 0\n-94 -176 -60 0\n-158 -112 -60 0\n-31 -120 -188 0\n-31 -184 -124 0\n-95 -56 -188 0\n-95 -184 -60 0\n-159 -56 -124 0\n-159 -120 -60 0\n-38 -111 -181 0\n-102 -175 -53 0\n-166 -47 -117 0\n-166 -111 -53 0\n-38 -176 -125 0\n-102 -176 -61 0\n-166 -48 -125 0\n-166 -112 -61 0\n-39 -120 -189 0\n-103 -184 -61 0\n-167 -56 -125 0\n-167 -120 -61 0\n-111 -184 -62 0\n-175 -120 -62 0\n-2 -2 385 0\n-385 -11 -11 386 0\n-386 -20 -20 387 0\n-387 -29 -29 388 0\n-387 -93 -29 0\n-387 -157 -157 0\n-388 -38 -38 389 0\n-388 -166 -166 0\n-389 -47 -47 390 0\n-389 -175 -175 0\n-390 -184 -184 0\n-2 -93 518 0\n-518 -11 -102 519 0\n-519 -20 -111 520 0\n-520 -93 -56 521 0\n-520 -93 -120 0\n-521 -102 -121 0\n-2 -175 609 0\n-609 -11 -184 610 0\n-610 -20 -185 611 0\n-611 -93 -2 612 0\n-612 -102 -11 613 0\n-612 -166 -11 0\n-613 -175 -20 0\n-2 -56 630 0\n-630 -11 -57 631 0\n-631 -20 -2 632 0\n-632 -93 -11 0\n-2 -57 672 0\n-672 -11 -2 673 0\n-673 -20 -11 674 0\n-674 -29 -20 675 0\n-674 -93 -20 0\n-675 -38 -29 676 0\n-675 -102 -29 0\n-676 -47 -38 677 0\n-676 -111 -38 0\n-677 -120 -47 0\n197 261 325 0\n198 262 326 0\n205 269 333 0\n206 270 334 0\n207 271 335 0\n208 272 336 0\n213 277 341 0\n214 278 342 0\n215 279 343 0\n216 280 344 0\n209 273 337 0\n222 286 350 0\n223 287 351 0\n224 288 352 0\n217 281 345 0\n218 282 346 0\n231 295 359 0\n232 296 360 0\n225 289 353 0\n226 290 354 0\n227 291 355 0\n240 304 368 0\n233 297 361 0\n234 298 362 0\n235 299 363 0\n236 300 364 0\n241 305 369 0\n242 306 370 0\n243 307 371 0\n244 308 372 0\n245 309 373 0\n250 314 378 0\n251 315 379 0\n252 316 380 0\n253 317 381 0\n254 318 382 0\n723 724 725 0\n-723 222 0\n-723 29 30 0\n-723 30 38 0\n-724 286 0\n-724 93 94 0\n-724 94 102 0\n-725 350 0\n-725 157 158 0\n726 727 728 0\n-726 231 0\n-726 38 39 0\n-726 39 47 0\n-727 295 0\n-727 102 103 0\n-727 103 111 0\n-728 359 0\n-728 166 167 0\n-728 167 175 0\n729 730 731 0\n-729 240 0\n-729 47 48 0\n-730 304 0\n-730 111 112 0\n-730 112 120 0\n-731 368 0\n-731 175 176 0\n-731 176 184 0\n732 733 734 0\n-732 241 0\n-732 49 57 0\n-733 305 0\n-733 120 113 0\n-734 369 0\n-734 184 177 0\n735 736 737 0\n-735 250 0\n-735 57 58 0\n-736 314 0\n-736 122 66 0\n-737 378 0\n-737 186 130 0\n741 742 743 0\n-741 205 0\n-741 13 21 29 0\n-742 269 0\n-742 75 76 77 0\n-743 333 0\n-743 139 141 155 157 0\n744 745 746 0\n-744 214 0\n-744 22 30 38 0\n-745 278 0\n-745 84 85 86 0\n-745 84 86 100 102 0\n-746 342 0\n-746 148 149 150 0\n-746 148 150 164 166 0\n747 748 749 0\n-747 223 0\n-747 29 30 31 0\n-747 30 31 38 39 0\n-747 29 31 45 47 0\n-747 31 39 47 0\n-748 287 0\n-748 93 94 95 0\n-748 94 95 102 103 0\n-748 93 95 109 111 0\n-748 95 103 111 0\n-749 351 0\n-749 157 158 159 0\n-749 157 159 173 175 0\n750 751 752 0\n-750 232 0\n-750 38 39 40 0\n-750 39 40 47 48 0\n-751 296 0\n-751 102 103 104 0\n-751 102 104 118 120 0\n-751 104 112 120 0\n-752 360 0\n-752 166 167 168 0\n-752 166 168 182 184 0\n-752 168 176 184 0\n753 754 755 0\n-753 233 0\n-753 41 49 57 0\n-754 297 0\n-754 111 112 105 0\n-755 361 0\n-755 175 176 169 0\n756 757 758 0\n-756 242 0\n-756 56 49 50 0\n-756 49 50 57 58 0\n-757 306 0\n-757 120 114 72 66 0\n-757 114 122 66 0\n-758 370 0\n-758 184 178 136 130 0\n-758 178 186 130 0\n759 760 761 0\n-759 251 0\n-759 57 58 59 0\n-760 315 0\n-760 123 67 75 0\n-761 379 0\n-761 186 187 130 131 0\n-761 187 131 139 0\n762 763 764 0\n-762 197 0\n-762 5 13 21 29 0\n-763 261 0\n-763 66 67 68 69 0\n-763 67 68 69 75 76 77 0\n-764 325 0\n765 766 767 0\n-765 206 0\n-765 14 22 30 38 0\n-766 75 76 77 78 0\n-766 75 76 78 99 100 102 0\n-766 75 78 91 94 99 102 0\n-767 334 0\n768 769 770 0\n-768 215 0\n-768 21 22 23 29 30 31 0\n-768 22 23 30 31 38 39 0\n-768 23 31 39 47 0\n-769 279 0\n-769 84 85 86 87 0\n-769 85 86 87 93 94 95 0\n-769 84 86 87 100 102 103 0\n-769 84 85 87 108 109 111 0\n-769 84 87 100 103 108 111 0\n-770 343 0\n-770 148 149 150 151 0\n-770 148 150 151 164 166 167 0\n-770 150 151 158 159 166 167 0\n-770 148 149 151 172 173 175 0\n-770 149 151 157 159 173 175 0\n-770 148 151 164 167 172 175 0\n-770 151 159 167 175 0\n771 772 773 0\n-771 224 0\n-772 288 0\n-772 93 94 95 96 0\n-772 94 95 96 102 103 104 0\n-772 94 96 102 104 118 120 0\n-772 93 96 109 112 117 120 0\n-772 96 104 112 120 0\n-773 352 0\n-773 157 158 159 160 0\n-773 157 158 160 181 182 184 0\n-773 158 160 166 168 182 184 0\n-773 157 160 173 176 181 184 0\n-773 160 168 176 184 0\n774 775 776 0\n-774 225 0\n-775 289 0\n-775 102 103 104 97 0\n-776 353 0\n-776 166 167 168 161 0\n-776 166 168 161 182 184 177 0\n-776 168 161 176 169 184 177 0\n-776 167 161 175 169 191 185 0\n-776 166 161 182 177 190 185 0\n777 778 779 0\n-777 234 0\n-777 47 41 42 63 57 58 0\n-778 298 0\n-778 111 112 105 106 0\n-778 111 112 106 71 72 66 0\n-778 112 106 120 114 72 66 0\n-778 111 106 127 122 71 66 0\n-778 106 114 122 66 0\n-779 362 0\n-779 175 176 169 170 0\n-779 175 176 170 135 136 130 0\n-779 176 170 184 178 136 130 0\n-779 175 170 191 186 135 130 0\n-779 170 178 186 130 0\n780 781 782 0\n-780 243 0\n-780 56 49 50 51 0\n-780 49 50 51 57 58 59 0\n-781 307 0\n-781 114 115 122 123 66 67 0\n-781 115 123 67 75 0\n-782 371 0\n-782 184 177 179 144 137 139 0\n-782 184 179 136 131 144 139 0\n783 784 785 0\n-783 252 0\n-783 57 58 59 60 0\n-784 316 0\n-784 124 68 76 84 0\n-785 380 0\n-785 188 132 140 148 0\n786 787 788 0\n-786 6 14 22 30 38 0\n-787 262 0\n-787 66 68 70 82 84 86 98 100 102 0\n-788 326 0\n789 790 791 0\n-789 207 0\n-789 14 15 22 23 30 31 38 39 0\n-789 15 23 31 39 47 0\n-790 271 0\n-790 75 76 77 78 79 0\n-790 75 76 79 99 100 103 107 108 111 0\n-790 75 79 91 95 99 103 107 111 0\n-791 335 0\n-791 139 140 141 142 143 0\n-791 139 143 155 159 163 167 171 175 0\n792 793 794 0\n-792 216 0\n-793 280 0\n-793 84 85 86 87 88 0\n-793 84 85 87 88 108 109 111 112 0\n-793 85 87 88 93 95 96 109 111 112 0\n-793 84 87 88 100 103 104 108 111 112 0\n-793 87 88 95 96 103 104 111 112 0\n-793 84 85 86 88 116 117 118 120 0\n-793 84 86 88 100 102 104 116 118 120 0\n-793 86 88 94 96 102 104 118 120 0\n-793 84 85 88 108 109 112 116 117 120 0\n-793 84 88 100 104 108 112 116 120 0\n-793 88 96 104 112 120 0\n-794 344 0\n-794 148 149 150 151 152 0\n-794 148 150 151 152 164 166 167 168 0\n-794 148 149 151 152 172 173 175 176 0\n-794 148 151 152 164 167 168 172 175 176 0\n-794 148 149 150 152 180 181 182 184 0\n-794 148 150 152 164 166 168 180 182 184 0\n-794 150 152 158 160 166 168 182 184 0\n-794 148 149 152 172 173 176 180 181 184 0\n-794 149 152 157 160 173 176 181 184 0\n-794 148 152 164 168 172 176 180 184 0\n-794 152 160 168 176 184 0\n795 796 797 0\n-795 217 0\n-796 93 94 95 96 89 0\n-797 345 0\n798 799 800 0\n-798 226 0\n-799 290 0\n-799 102 103 104 97 98 0\n-799 102 103 104 98 70 71 72 66 0\n-799 104 98 112 106 120 114 72 66 0\n-799 102 103 98 126 127 122 70 71 66 0\n-799 103 98 111 106 127 122 71 66 0\n-799 102 98 118 114 126 122 70 66 0\n-799 98 106 114 122 66 0\n-800 354 0\n-800 166 167 168 161 162 0\n-800 167 168 161 162 175 176 169 170 0\n-800 166 167 161 162 190 191 185 186 0\n-800 166 167 168 162 134 135 136 130 0\n-800 167 168 162 175 176 170 135 136 130 0\n-800 166 168 162 182 184 178 134 136 130 0\n-800 168 162 176 170 184 178 136 130 0\n-800 166 167 162 190 191 186 134 135 130 0\n-800 167 162 175 170 191 186 135 130 0\n-800 166 162 182 178 190 186 134 130 0\n-800 162 170 178 186 130 0\n801 802 803 0\n-801 235 0\n-801 41 42 43 49 50 51 57 58 59 0\n-802 299 0\n-802 111 112 105 106 107 0\n-802 106 107 114 115 122 123 66 67 0\n-802 111 112 105 107 79 80 73 75 0\n-802 111 112 107 71 72 67 79 80 75 0\n-802 112 107 120 115 72 67 80 75 0\n-802 111 107 127 123 71 67 79 75 0\n-802 107 115 123 67 75 0\n-803 363 0\n-803 175 176 169 170 171 0\n-803 175 176 170 171 135 136 130 131 0\n-803 170 171 178 179 186 187 130 131 0\n-803 175 176 169 171 143 144 137 139 0\n-803 176 169 171 184 177 179 144 137 139 0\n-803 175 169 171 191 185 187 143 137 139 0\n-803 176 171 184 179 136 131 144 139 0\n-803 175 171 191 187 135 131 143 139 0\n-803 171 179 187 131 139 0\n804 805 806 0\n-804 244 0\n-804 56 49 50 51 52 0\n-804 49 50 51 52 57 58 59 60 0\n-805 308 0\n-805 120 116 72 68 80 76 88 84 0\n-805 116 124 68 76 84 0\n-806 372 0\n-806 180 188 132 140 148 0\n807 808 809 0\n-807 253 0\n-807 57 58 59 60 61 0\n-807 57 58 59 61 25 26 27 29 0\n-807 57 58 61 17 18 21 25 26 29 0\n-807 57 61 9 13 17 21 25 29 0\n-808 317 0\n-808 122 123 124 125 66 67 68 69 0\n-808 125 69 77 85 93 0\n-809 381 0\n-809 186 189 130 133 146 149 154 157 0\n-809 189 133 141 149 157 0\n810 811 812 0\n-810 199 0\n-810 6 7 14 15 22 23 30 31 38 39 0\n-810 7 15 23 31 39 47 0\n-811 263 0\n-811 66 67 68 69 70 71 0\n-812 327 0\n813 814 815 0\n-813 208 0\n-814 272 0\n-814 75 76 77 78 79 80 0\n-814 76 77 78 79 80 84 85 86 87 88 0\n-814 75 76 78 79 80 99 100 102 103 104 0\n-814 76 78 79 80 84 86 87 88 100 102 103 104 0\n-814 76 77 79 80 84 85 87 88 108 109 111 112 0\n-814 79 80 87 88 95 96 103 104 111 112 0\n-814 75 78 80 91 94 96 99 102 104 115 118 120 0\n-814 76 77 80 84 85 88 108 109 112 116 117 120 0\n-815 336 0\n-815 139 140 141 142 143 144 0\n-815 140 141 142 143 144 148 149 150 151 152 0\n-815 139 141 142 143 144 155 157 158 159 160 0\n-815 141 142 143 144 149 150 151 152 157 158 159 160 0\n-815 140 142 143 144 148 150 151 152 164 166 167 168 0\n-815 139 141 143 144 155 157 159 160 171 173 175 176 0\n-815 139 141 142 144 155 157 158 160 179 181 182 184 0\n-815 139 140 142 144 163 164 166 168 179 180 182 184 0\n-815 140 142 144 148 150 152 164 166 168 180 182 184 0\n-815 139 141 144 155 157 160 171 173 176 179 181 184 0\n-815 141 144 149 152 157 160 173 176 181 184 0\n-815 144 152 160 168 176 184 0\n816 817 818 0\n-816 209 0\n-817 84 85 86 87 88 81 0\n-818 337 0\n822 823 824 0\n-822 227 0\n-823 291 0\n-823 99 107 115 123 67 75 0\n-824 355 0\n-824 166 167 168 161 162 163 0\n-824 167 168 161 162 163 175 176 169 170 171 0\n-824 168 161 162 163 176 169 170 171 184 177 178 179 0\n-824 166 167 161 162 163 190 191 185 186 187 0\n-824 166 167 168 162 163 134 135 136 130 131 0\n-824 168 162 163 176 170 171 184 178 179 136 130 131 0\n-824 166 167 162 163 190 191 186 187 134 135 130 131 0\n-824 167 162 163 175 170 171 191 186 187 135 130 131 0\n-824 162 163 170 171 178 179 186 187 130 131 0\n-824 166 167 168 161 163 142 143 144 137 139 0\n-824 167 168 161 163 175 176 169 171 143 144 137 139 0\n-824 166 167 161 163 190 191 185 187 142 143 137 139 0\n-824 161 163 169 171 177 179 185 187 137 139 0\n-824 168 163 176 171 184 179 136 131 144 139 0\n-824 166 167 163 190 191 187 134 135 131 142 143 139 0\n-824 167 163 175 171 191 187 135 131 143 139 0\n-824 163 171 179 187 131 139 0\n825 826 827 0\n-825 236 0\n-825 47 48 41 42 43 44 0\n-825 48 41 42 43 44 56 49 50 51 52 0\n-825 47 41 42 43 44 63 57 58 59 60 0\n-825 41 42 43 44 49 50 51 52 57 58 59 60 0\n-826 300 0\n-826 111 112 105 106 107 108 0\n-826 112 108 120 116 72 68 80 76 88 84 0\n-826 108 116 124 68 76 84 0\n-827 364 0\n-827 175 170 171 172 191 186 187 188 135 130 131 132 0\n-827 170 171 172 178 179 180 186 187 188 130 131 132 0\n-827 175 176 170 172 135 136 130 132 151 152 146 148 0\n-827 170 172 178 180 186 188 130 132 146 148 0\n-827 169 172 177 180 185 188 137 140 145 148 0\n-827 175 172 191 188 135 132 143 140 151 148 0\n-827 172 180 188 132 140 148 0\n828 829 830 0\n-828 245 0\n-828 56 49 50 51 52 53 0\n-828 49 50 51 52 53 57 58 59 60 61 0\n-828 49 53 57 61 9 13 17 21 25 29 0\n-828 53 61 5 13 21 29 0\n-829 309 0\n-829 120 113 114 115 116 117 0\n-829 113 114 115 116 117 121 122 123 124 125 0\n-829 120 114 115 116 117 72 66 67 68 69 0\n-829 114 115 116 117 122 123 124 125 66 67 68 69 0\n-830 373 0\n-830 184 177 178 179 180 181 0\n-830 178 179 180 181 186 187 188 189 130 131 132 133 0\n-830 181 189 133 141 149 157 0\n831 832 833 0\n-831 254 0\n-831 57 58 59 60 61 62 0\n-831 57 61 62 9 13 14 17 21 22 25 29 30 0\n-831 57 58 59 60 62 33 34 35 36 38 0\n-831 57 58 59 62 25 26 27 30 33 34 35 38 0\n-831 57 58 62 17 18 22 25 26 30 33 34 38 0\n-831 57 62 9 14 17 22 25 30 33 38 0\n-831 62 6 14 22 30 38 0\n-832 318 0\n-832 121 122 123 124 125 126 0\n-832 122 123 124 125 126 66 67 68 69 70 0\n-833 382 0\n-833 189 190 133 134 141 142 149 150 157 158 0\n-833 190 134 142 150 158 166 0\n"
 "1442 -8 0 775 181 0\n1443 -72 0 776 355 0\n1444 -136 0 777 555 0\n1445 -9 0 778 182 0\n1446 -73 0 779 356 0\n1447 -137 0 780 556 0\n1448 -18 0 781 189 0\n1449 -82 0 782 362 0\n1450 -146 0 783 562 0\n1451 -27 0 784 197 0\n1452 -91 0 785 368 0\n1453 -155 0 786 569 0\n1454 -36 0 788 205 0\n1455 -100 0 789 376 0\n1456 -164 0 790 576 0\n1457 -45 0 792 213 0\n1458 -109 0 793 384 0\n1459 -173 0 794 584 0\n1460 -54 0 796 221 0\n1461 -118 0 797 392 0\n1462 -182 0 798 592 0\n1463 -63 0 800 228 0\n1464 -127 0 801 400 0\n1465 -191 0 802 600 0\n1466 -66 0 803 1 0\n1467 -130 0 803 2 0\n1468 194 0 803 177 0\n1469 -208 0 1468 775 231 0\n1470 -209 0 1468 781 256 0\n1471 -16 0 1469 187 0\n1472 -17 0 1470 188 0\n1473 -75 0 804 27 0\n1474 -139 0 804 28 0\n1475 203 0 804 183 0\n1476 195 0 1475 1468 229 0\n1477 -216 0 1475 1469 243 0\n1478 -218 0 1475 784 272 0\n1479 -217 0 1476 784 271 0\n1480 -24 0 1477 194 0\n1481 -26 0 1478 196 0\n1482 -25 0 1479 195 0\n1483 -84 0 805 67 0\n1484 -148 0 805 68 0\n1485 212 0 805 190 0\n1486 196 0 1485 1476 232 0\n1487 204 0 1485 1475 239 0\n1488 -224 0 1485 1477 260 0\n1489 -227 0 1485 788 288 0\n1490 -225 0 1486 788 286 0\n1491 -226 0 1487 788 287 0\n1492 -32 0 1488 201 0\n1493 -35 0 1489 204 0\n1494 -33 0 1490 202 0\n1495 -34 0 1491 203 0\n1496 -76 -153 0 803 806 0\n1497 -140 -89 0 803 807 0\n1498 -77 -161 0 803 808 0\n1499 -141 -97 0 803 809 0\n1500 -78 -169 0 803 810 0\n1501 -142 -105 0 803 811 0\n1502 -79 -177 0 803 812 0\n1503 -143 -113 0 803 813 0\n1504 -80 -185 0 803 814 0\n1505 -144 -121 0 803 815 0\n1506 -67 -153 0 805 816 0\n1507 -131 -89 0 805 817 0\n1508 -85 -162 0 804 844 0\n1509 -149 -98 0 804 845 0\n1510 -86 -170 0 804 846 0\n1511 -150 -106 0 804 847 0\n1512 -87 -178 0 804 848 0\n1513 -151 -114 0 804 849 0\n1514 -88 -186 0 804 850 0\n1515 -152 -122 0 804 851 0\n1516 -93 -163 0 805 884 0\n1517 -94 -171 0 805 885 0\n1518 -158 -107 0 805 886 0\n1519 -95 -179 0 805 887 0\n1520 -159 -115 0 805 888 0\n1521 -96 -187 0 805 889 0\n1522 -160 -123 0 805 890 0\n1523 385 0 803 955 0\n1524 386 0 1523 804 956 0\n1525 387 0 1524 805 957 0\n1526 -29 388 0 1525 958 0\n1527 -93 -29 0 1525 959 0\n1528 -157 0 1525 960 0\n1529 -388 -38 389 0 961 0\n1530 -388 -166 0 962 0\n1531 -389 -47 390 0 963 0\n1532 -389 -175 0 964 0\n1533 -390 -184 0 965 0\n1534 -93 518 0 803 966 0\n1535 -518 -102 519 0 804 967 0\n1536 -519 -111 520 0 805 968 0\n1537 -175 609 0 803 972 0\n1538 -609 -184 610 0 804 973 0\n1539 -610 -185 611 0 805 974 0\n1540 -611 -93 612 0 803 975 0\n1541 -612 -102 613 0 804 976 0\n1542 -612 -166 0 804 977 0\n1543 -613 -175 0 805 978 0\n1544 -56 630 0 803 979 0\n1545 -630 -57 631 0 804 980 0\n1546 -631 632 0 805 803 981 0\n1547 -632 -93 0 804 982 0\n1548 -57 672 0 803 983 0\n1549 -672 673 0 804 803 984 0\n1550 -673 674 0 805 804 985 0\n1551 -674 -29 675 0 805 986 0\n1552 -674 -93 0 805 987 0\n1553 272 336 0 1469 998 0\n1554 280 344 0 1477 1002 0\n1555 273 337 0 1470 1003 0\n1556 288 352 0 1488 1006 0\n1557 281 345 0 1479 1007 0\n1558 282 346 0 1478 1008 0\n1559 289 353 0 1490 1011 0\n1560 290 354 0 1491 1012 0\n1561 291 355 0 1489 1013 0\n1562 -725 158 0 1528 1037 0\n1563 -736 122 0 1466 1068 0\n1564 -737 186 0 1467 1070 0\n1565 -742 76 77 0 1473 1075 0\n1566 -743 141 0 1474 1453 1528 1077 0\n1567 -745 85 86 0 1483 1082 0\n1568 -745 86 102 0 1483 1455 1083 0\n1569 -746 149 150 0 1484 1085 0\n1570 -746 150 166 0 1484 1456 1086 0\n1571 -747 29 31 47 0 1457 1091 0\n1572 -748 93 95 111 0 1458 1096 0\n1573 -749 158 159 0 1528 1099 0\n1574 -749 159 175 0 1528 1459 1100 0\n1575 -751 102 104 120 0 1461 1107 0\n1576 -752 166 168 184 0 1462 1111 0\n1577 -757 120 114 0 1443 1466 1125 0\n1578 -757 114 122 0 1466 1126 0\n1579 -758 184 178 0 1444 1467 1128 0\n1580 -758 178 186 0 1467 1129 0\n1581 -760 123 67 0 1473 1134 0\n1582 -761 186 187 131 0 1467 1136 0\n1583 -761 187 131 0 1474 1137 0\n1584 -763 67 68 69 0 1466 1142 0\n1585 -763 67 68 69 76 77 0 1473 1143 0\n1586 -766 76 77 78 0 1473 1148 0\n1587 -766 76 78 99 102 0 1473 1455 1149 0\n1588 -766 78 94 99 102 0 1473 1452 1150 0\n1589 -769 85 86 87 0 1483 1158 0\n1590 -769 86 87 102 103 0 1483 1455 1160 0\n1591 -769 85 87 108 111 0 1483 1458 1161 0\n1592 -769 87 103 108 111 0 1483 1455 1162 0\n1593 -770 149 150 151 0 1484 1164 0\n1594 -770 150 151 166 167 0 1484 1456 1165 0\n1595 -770 149 151 172 175 0 1484 1459 1167 0\n1596 -770 149 151 159 175 0 1528 1459 1168 0\n1597 -770 151 167 172 175 0 1484 1456 1169 0\n1598 -771 0 1488 1172 0\n1599 -772 94 96 102 104 120 0 1461 1176 0\n1600 -772 93 96 112 117 120 0 1458 1177 0\n1601 -773 158 159 160 0 1528 1180 0\n1602 -773 158 160 181 184 0 1528 1462 1181 0\n1603 -773 158 160 166 168 184 0 1462 1182 0\n1604 -773 160 176 181 184 0 1528 1459 1183 0\n1605 -774 0 1490 1186 0\n1606 -776 166 168 161 184 177 0 1462 1191 0\n1607 -776 167 161 175 169 185 0 1465 1193 0\n1608 -776 166 161 177 190 185 0 1462 1194 0\n1609 -777 47 41 42 57 58 0 1463 1197 0\n1610 -778 111 112 106 71 0 1443 1466 1200 0\n1611 -778 112 106 120 114 0 1443 1466 1201 0\n1612 -778 111 106 122 71 0 1464 1466 1202 0\n1613 -778 106 114 122 0 1466 1203 0\n1614 -779 175 176 170 135 0 1444 1467 1206 0\n1615 -779 176 170 184 178 0 1444 1467 1207 0\n1616 -779 175 170 186 135 0 1465 1467 1208 0\n1617 -779 170 178 186 0 1467 1209 0\n1618 -781 114 115 122 123 67 0 1466 1215 0\n1619 -781 115 123 67 0 1473 1216 0\n1620 -782 184 177 179 144 0 1447 1474 1218 0\n1621 -782 184 179 131 144 0 1444 1474 1219 0\n1622 -784 124 68 76 0 1483 1224 0\n1623 -785 188 132 140 0 1484 1226 0\n1624 -787 68 70 86 98 102 0 1466 1449 1483 1455 1230 0\n1625 -790 76 77 78 79 0 1473 1237 0\n1626 -790 76 79 99 103 107 108 111 0 1473 1455 1238 0\n1627 -790 79 95 99 103 107 111 0 1473 1452 1239 0\n1628 -791 140 141 142 143 0 1474 1241 0\n1629 -791 143 159 163 167 171 175 0 1474 1453 1242 0\n1630 -792 0 1477 1244 0\n1631 -793 85 86 87 88 0 1483 1246 0\n1632 -793 85 87 88 108 111 112 0 1483 1458 1247 0\n1633 -793 85 87 88 93 95 96 111 112 0 1458 1248 0\n1634 -793 87 88 103 104 108 111 112 0 1483 1455 1249 0\n1635 -793 85 86 88 116 117 120 0 1483 1461 1251 0\n1636 -793 86 88 102 104 116 120 0 1483 1455 1461 1252 0\n1637 -793 86 88 94 96 102 104 120 0 1461 1253 0\n1638 -793 85 88 108 112 116 117 120 0 1483 1458 1254 0\n1639 -793 88 104 108 112 116 120 0 1483 1455 1255 0\n1640 -794 149 150 151 152 0 1484 1258 0\n1641 -794 150 151 152 166 167 168 0 1484 1456 1259 0\n1642 -794 149 151 152 172 175 176 0 1484 1459 1260 0\n1643 -794 151 152 167 168 172 175 176 0 1484 1456 1261 0\n1644 -794 149 150 152 180 181 184 0 1484 1462 1262 0\n1645 -794 150 152 166 168 180 184 0 1484 1456 1462 1263 0\n1646 -794 150 152 158 160 166 168 184 0 1462 1264 0\n1647 -794 149 152 172 176 180 181 184 0 1484 1459 1265 0\n1648 -794 149 152 160 176 181 184 0 1528 1459 1266 0\n1649 -794 152 168 172 176 180 184 0 1484 1456 1267 0\n1650 -795 0 1479 1270 0\n1651 -798 0 1491 1274 0\n1652 -799 102 103 104 98 70 71 0 1443 1466 1277 0\n1653 -799 104 98 112 106 120 114 0 1443 1466 1278 0\n1654 -799 102 103 98 126 122 70 71 0 1464 1466 1279 0\n1655 -799 103 98 111 106 122 71 0 1464 1466 1280 0\n1656 -799 102 98 114 126 122 70 0 1461 1466 1281 0\n1657 -799 98 106 114 122 0 1466 1282 0\n1658 -800 166 167 161 162 190 185 186 0 1465 1286 0\n1659 -800 166 167 168 162 134 135 0 1444 1467 1287 0\n1660 -800 167 168 162 175 176 170 135 0 1444 1467 1288 0\n1661 -800 166 168 162 184 178 134 0 1462 1444 1467 1289 0\n1662 -800 168 162 176 170 184 178 0 1444 1467 1290 0\n1663 -800 166 167 162 190 186 134 135 0 1465 1467 1291 0\n1664 -800 167 162 175 170 186 135 0 1465 1467 1292 0\n1665 -800 166 162 178 190 186 134 0 1462 1467 1293 0\n1666 -800 162 170 178 186 0 1467 1294 0\n1667 -802 106 107 114 115 122 123 67 0 1466 1300 0\n1668 -802 111 112 105 107 79 80 0 1446 1473 1301 0\n1669 -802 111 112 107 71 67 79 80 0 1443 1473 1302 0\n1670 -802 112 107 120 115 67 80 0 1443 1473 1303 0\n1671 -802 111 107 123 71 67 79 0 1464 1473 1304 0\n1672 -802 107 115 123 67 0 1473 1305 0\n1673 -803 175 176 170 171 135 131 0 1444 1467 1308 0\n1674 -803 170 171 178 179 186 187 131 0 1467 1309 0\n1675 -803 175 176 169 171 143 144 0 1447 1474 1310 0\n1676 -803 176 169 171 184 177 179 144 0 1447 1474 1311 0\n1677 -803 175 169 171 185 187 143 0 1465 1447 1474 1312 0\n1678 -803 176 171 184 179 131 144 0 1444 1474 1313 0\n1679 -803 175 171 187 135 131 143 0 1465 1474 1314 0\n1680 -803 171 179 187 131 0 1474 1315 0\n1681 -805 120 116 68 80 76 88 0 1443 1483 1321 0\n1682 -805 116 124 68 76 0 1483 1322 0\n1683 -806 180 188 132 140 0 1484 1324 0\n1684 -807 57 58 59 61 29 0 1482 1481 1451 1328 0\n1685 -807 57 58 61 21 29 0 1472 1448 1482 1481 1329 0\n1686 -807 57 61 13 21 29 0 1445 1472 1482 1330 0\n1687 -808 122 123 124 125 67 68 69 0 1466 1332 0\n1688 -809 186 189 133 149 154 0 1467 1450 1528 1335 0\n1689 -809 189 133 141 149 0 1528 1336 0\n1690 -811 67 68 69 70 71 0 1466 1342 0\n1691 -813 0 1469 1345 0\n1692 -814 76 77 78 79 80 0 1473 1347 0\n1693 -814 76 77 78 79 80 85 86 87 88 0 1483 1348 0\n1694 -814 76 78 79 80 99 102 103 104 0 1473 1455 1349 0\n1695 -814 76 78 79 80 86 87 88 102 103 104 0 1483 1455 1350 0\n1696 -814 76 77 79 80 85 87 88 108 111 112 0 1483 1458 1351 0\n1697 -814 78 80 94 96 99 102 104 115 120 0 1473 1452 1461 1353 0\n1698 -814 76 77 80 85 88 108 112 116 117 120 0 1483 1458 1354 0\n1699 -815 140 141 142 143 144 0 1474 1356 0\n1700 -815 140 141 142 143 144 149 150 151 152 0 1484 1357 0\n1701 -815 141 142 143 144 158 159 160 0 1474 1453 1528 1358 0\n1702 -815 141 142 143 144 149 150 151 152 158 159 160 0 1528 1359 0\n1703 -815 140 142 143 144 150 151 152 166 167 168 0 1484 1456 1360 0\n1704 -815 141 143 144 159 160 171 175 176 0 1474 1453 1528 1459 1361 0\n1705 -815 141 142 144 158 160 179 181 184 0 1474 1453 1528 1462 1362 0\n1706 -815 140 142 144 163 166 168 179 180 184 0 1474 1456 1462 1363 0\n1707 -815 140 142 144 150 152 166 168 180 184 0 1484 1456 1462 1364 0\n1708 -815 141 144 160 171 176 179 181 184 0 1474 1453 1528 1459 1365 0\n1709 -815 141 144 149 152 160 176 181 184 0 1528 1459 1366 0\n1710 -816 0 1470 1369 0\n1711 -817 85 86 87 88 81 0 1483 1370 0\n1712 -822 0 1489 1373 0\n1713 -823 99 107 115 123 67 0 1473 1375 0\n1714 -824 166 167 161 162 163 190 185 186 187 0 1465 1380 0\n1715 -824 166 167 168 162 163 134 135 131 0 1444 1467 1381 0\n1716 -824 168 162 163 176 170 171 184 178 179 131 0 1444 1467 1382 0\n1717 -824 166 167 162 163 190 186 187 134 135 131 0 1465 1467 1383 0\n1718 -824 167 162 163 175 170 171 186 187 135 131 0 1465 1467 1384 0\n1719 -824 162 163 170 171 178 179 186 187 131 0 1467 1385 0\n1720 -824 166 167 168 161 163 142 143 144 0 1447 1474 1386 0\n1721 -824 167 168 161 163 175 176 169 171 143 144 0 1447 1474 1387 0\n1722 -824 166 167 161 163 190 185 187 142 143 0 1465 1447 1474 1388 0\n1723 -824 161 163 169 171 177 179 185 187 0 1447 1474 1389 0\n1724 -824 168 163 176 171 184 179 131 144 0 1444 1474 1390 0\n1725 -824 166 167 163 190 187 134 135 131 142 143 0 1465 1474 1391 0\n1726 -824 167 163 175 171 187 135 131 143 0 1465 1474 1392 0\n1727 -824 163 171 179 187 131 0 1474 1393 0\n1728 -825 47 41 42 43 44 57 58 59 60 0 1463 1398 0\n1729 -826 112 108 120 116 68 80 76 88 0 1443 1483 1402 0\n1730 -826 108 116 124 68 76 0 1483 1403 0\n1731 -827 175 170 171 172 186 187 188 135 131 132 0 1465 1467 1405 0\n1732 -827 170 171 172 178 179 180 186 187 188 131 132 0 1467 1406 0\n1733 -827 175 176 170 172 135 132 151 152 0 1444 1467 1450 1484 1407 0\n1734 -827 170 172 178 180 186 188 132 0 1467 1450 1484 1408 0\n1735 -827 169 172 177 180 185 188 140 145 0 1447 1484 1409 0\n1736 -827 175 172 188 135 132 143 140 151 0 1465 1484 1410 0\n1737 -827 172 180 188 132 140 0 1484 1411 0\n1738 -828 49 53 57 61 13 21 29 0 1445 1472 1482 1416 0\n1739 -829 120 114 115 116 117 67 68 69 0 1443 1466 1421 0\n1740 -829 114 115 116 117 122 123 124 125 67 68 69 0 1466 1422 0\n1741 -830 178 179 180 181 186 187 188 189 131 132 133 0 1467 1425 0\n1742 -830 181 189 133 141 149 0 1528 1426 0\n1743 -831 57 61 62 13 14 21 22 29 30 0 1445 1472 1482 1430 0\n1744 -831 57 58 59 60 62 38 0 1494 1495 1493 1454 1431 0\n1745 -831 57 58 59 62 30 38 0 1482 1481 1451 1494 1495 1493 1432 0\n1746 -831 57 58 62 22 30 38 0 1472 1448 1482 1481 1494 1495 1433 0\n1747 -831 57 62 14 22 30 38 0 1445 1472 1482 1494 1434 0\n1748 -832 122 123 124 125 126 67 68 69 70 0 1466 1438 0\n1749 -833 189 190 133 134 141 142 149 150 158 0 1528 1440 0\n1750 -121 143 142 141 140 0 779 1691 394 1505 428 1699 1346 1344 0\n1751 -143 71 135 7 49 0 780 560 1503 638 16 587 0\n1752 78 76 102 271 99 104 80 -814 0 360 1692 1694 358 378 421 0\n1753 -123 723 -783 -304 -112 58 57 0 785 98 396 1222 463 934 459 1562 1033 1029 0\n1754 167 166 727 381 104 120 168 750 0 800 793 1110 1046 1101 1038 1108 1039 386 348 504 1027 0\n1755 141 334 335 143 160 -121 -815 0 559 1505 1750 557 626 627 570 571 1701 0\n1756 -674 240 0 1528 1459 1458 1457 1552 787 1526 1551 1530 989 136 1529 988 1532 991 795 214 1531 990 312 1533 992 222 799 0\n1757 -121 184 176 179 171 -93 -5 131 0 785 1712 369 453 1374 1372 1516 1505 834 1724 0\n1758 -123 86 151 87 85 149 150 0 1630 100 102 1631 1640 1243 0\n1759 -295 122 290 123 -829 117 -285 69 68 67 0 785 789 801 453 480 546 479 478 390 398 539 389 388 397 1740 0\n1760 -295 290 123 -829 117 -285 69 68 67 0 785 789 453 480 479 478 1759 390 389 388 395 1739 520 393 0\n1761 -122 151 149 150 0 782 1630 395 1515 446 1640 1245 1243 0\n1762 -180 103 158 111 29 47 0 122 127 128 1571 1097 1573 1087 0\n1763 206 746 270 85 382 777 0 1475 798 782 241 996 1079 733 756 1078 588 595 1081 1567 439 1510 1198 1617 1195 0\n1764 -53 -175 47 -723 0 1479 1478 784 1488 796 790 1456 1528 1455 1454 793 1030 280 215 278 211 277 210 276 209 141 145 146 220 942 1041 1043 332 1038 206 1046 1032 577 1530 108 695 1526 1396 1404 105 1394 369 1400 494 0\n1765 -388 102 389 0 1530 1529 791 0\n1766 -123 159 158 0 785 1598 396 1522 463 1601 1173 1171 0\n1767 -223 152 88 188 160 123 124 0 1485 800 1492 1480 259 347 345 226 225 129 97 1521 0\n1768 -144 57 0 60 64 66 1066 1563 1564 1064 0\n1769 95 31 -772 96 159 180 94 309 52 0 119 1174 390 369 514 0\n1770 -93 162 168 166 167 161 0 785 1712 369 1516 453 1377 1374 1372 0\n1771 -115 -772 749 760 94 -149 47 131 0 785 1485 800 802 1173 463 563 389 895 461 1041 371 1093 1087 1088 259 345 1131 1025 1130 761 1583 651 1521 1045 1174 1038 369 1042 455 0\n1772 -308 38 -303 0 793 789 1528 498 480 514 475 369 377 787 791 1526 1530 0\n1773 -159 123 67 780 0 786 571 1520 676 1619 1217 1210 0\n1774 -178 -778 170 106 -111 42 0 801 798 385 549 55 588 869 1613 733 395 559 533 37 359 0\n1775 -30 95 -772 160 159 96 152 123 88 188 -111 56 52 0 793 385 498 109 925 1174 1769 369 200 514 1767 397 936 522 799 393 0\n1776 30 95 223 159 -111 -723 0 793 796 797 790 163 1574 1088 1087 200 385 498 391 1030 331 219 1031 1032 106 198 206 941 1094 274 332 370 207 220 515 390 1022 119 700 918 578 140 0\n1777 -140 93 95 94 96 0 780 1650 557 1497 625 1271 1272 1269 0\n1778 -158 -188 -723 0 796 790 798 1488 789 597 704 1109 1030 331 111 570 1031 1032 737 198 921 137 1022 275 480 1102 378 1101 1106 0\n1779 30 -188 47 131 -723 0 1485 796 790 802 1488 789 785 597 764 1098 571 704 1109 1030 280 1756 1550 1549 1548 1768 258 329 1211 331 219 1031 1032 198 921 137 275 1102 1101 1106 1575 142 378 918 176 935 480 1092 390 1087 119 1093 1519 461 1621 1214 1210 0\n1780 -341 187 -824 163 373 131 0 794 712 735 582 589 1727 0\n1781 -95 23 87 151 51 0 785 371 1519 461 84 389 0\n1782 123 340 -30 759 59 58 747 252 120 131 67 -222 0 1485 796 1488 786 801 1598 1492 782 776 794 111 226 280 1756 1550 1549 1548 258 329 1211 1049 1581 1773 1130 1573 1135 1583 1087 679 1521 1093 572 1556 1179 541 406 1171 397 1026 351 129 664 931 1554 1053 1178 446 1048 154 156 379 395 1054 1327 411 725 352 1334 1687 1325 0\n1783 -159 87 151 23 51 0 786 571 1520 676 84 589 0\n1784 -30 95 159 -56 123 -222 0 1486 1469 1477 1488 1487 1485 796 801 785 790 776 779 786 802 1480 1598 782 1492 1462 1461 1460 794 331 222 335 226 258 329 334 1131 225 245 326 333 1065 224 280 312 214 285 1088 200 270 255 174 1756 1550 1549 1548 218 217 236 322 216 219 109 111 1573 1087 1093 1094 461 541 106 369 389 397 1026 453 704 1561 692 689 566 1554 403 446 350 1067 1024 1581 1782 1064 757 1130 550 1564 997 1135 667 1514 427 679 761 1557 97 387 572 1179 1001 512 1521 1171 442 390 129 388 119 931 925 1762 1178 160 145 147 154 585 1415 1419 720 1412 1423 0\n1785 95 159 -56 123 -723 0 1488 1462 1461 1460 1030 280 222 312 214 285 1784 1031 1032 1776 1526 160 1529 1532 0\n1786 -87 184 756 0 782 365 1512 442 1579 1124 1120 0\n1787 -95 -56 -222 0 1486 1485 1488 775 1469 1477 1487 796 785 783 245 326 1121 175 1786 222 270 193 255 186 238 180 280 1756 1550 1549 1548 1768 258 329 1211 218 217 236 322 216 371 1519 461 1214 1210 1620 1781 20 22 1502 565 1513 1751 658 46 588 0\n1788 -56 123 -723 0 1487 1485 796 1477 783 1030 258 329 218 245 326 1121 174 175 222 270 193 1786 1787 1785 1783 565 1513 658 1577 1127 1120 0\n1789 -151 123 756 0 783 802 782 1480 565 1513 658 761 1127 596 1120 1577 1578 914 395 1515 446 97 366 0\n1790 -749 159 -723 0 1573 1574 111 1532 1031 1032 1529 1526 0\n1791 -122 -343 123 -723 0 784 802 783 1487 796 782 1480 1485 800 798 794 785 1030 245 326 658 1020 442 1157 365 761 596 1121 1789 258 329 218 278 395 1515 446 366 97 225 343 345 347 193 1153 1088 1781 1783 1152 1790 1087 1093 461 1021 736 564 1761 563 712 650 1017 577 457 1594 370 148 1094 1095 369 377 454 0\n1792 -770 342 -748 95 151 235 0 794 785 564 1593 563 712 650 1017 577 457 1594 370 148 1094 1095 369 377 454 0\n1793 -748 95 736 379 370 151 56 -222 0 784 1485 1487 796 782 785 798 1475 800 1465 1464 1463 245 326 1020 442 1157 258 329 278 1093 461 1021 736 1792 1152 1153 242 345 342 1025 1065 521 1064 393 1069 173 743 593 0\n1794 -223 736 187 123 0 1487 1485 800 783 1480 246 259 342 345 1065 225 1064 1069 1564 663 1514 566 97 0\n1795 -215 736 761 123 0 1475 800 783 776 242 345 342 1131 1065 1130 1064 1581 1069 350 663 403 1554 0\n1796 -343 123 -723 0 1485 1487 796 783 802 782 1030 245 326 1121 1789 1788 258 329 218 658 761 1020 596 1135 442 365 1791 1563 1794 1088 1795 193 1781 1783 1793 1790 1087 0\n1797 -111 300 -30 159 95 31 52 0 385 925 497 119 390 0\n1798 -93 -184 58 -179 -748 159 95 379 31 -723 0 796 1488 785 793 801 1030 280 1756 1550 1549 1548 331 219 106 369 1031 453 494 1561 767 1334 1797 1097 378 893 950 546 1685 1331 1325 0\n1799 93 159 95 223 -723 0 1088 1790 1087 1094 1572 109 1776 0\n1800 87 379 215 122 123 -723 0 1479 1478 784 1486 1488 1485 1487 796 798 785 793 1712 1462 1461 1460 794 802 801 782 790 1444 1443 1442 596 1030 245 326 1796 1001 442 1020 733 559 388 258 266 214 1163 1153 1152 259 1088 200 193 1121 1789 1788 280 1756 1550 1549 1548 329 218 217 236 322 216 331 219 215 278 211 277 210 276 209 1781 1783 1790 1087 1093 461 541 389 397 1799 106 369 1516 1031 453 494 108 110 1374 1400 1797 1396 1372 1394 160 1097 1591 1404 585 1764 926 147 148 378 363 695 720 774 1414 119 546 435 577 1423 599 590 398 1560 1412 732 700 684 686 558 557 560 1750 23 1420 594 21 752 749 553 550 1725 0\n1801 379 215 122 123 -723 0 1488 801 782 1487 796 1030 245 326 1121 1796 1001 442 1124 1120 537 1133 280 1756 1550 1549 1548 1135 1130 1800 1512 1786 1580 913 61 1132 0\n1802 95 -748 159 58 59 -184 215 -723 0 796 1488 1485 793 1462 1461 1460 794 801 593 1030 258 266 214 259 200 280 1756 1550 1549 1548 331 219 1799 106 369 1031 494 1797 160 1097 585 378 950 720 546 1684 746 1331 1334 1325 0\n1803 112 -188 67 96 124 58 59 120 352 122 123 240 0 1598 776 794 1556 406 351 1179 1171 1756 1550 1549 1548 1049 1053 1178 1048 154 156 379 921 1054 1684 411 725 352 1334 1687 1325 0\n1804 -87 215 122 123 -723 0 1485 782 1487 796 786 783 801 1480 776 1492 790 1488 1801 679 572 1030 245 326 1121 1796 1001 442 1124 1120 259 1088 280 1512 1786 1580 176 593 913 61 595 1514 678 663 571 1098 1005 566 1554 1087 541 97 403 397 1521 350 1802 938 129 597 704 1109 1803 931 1031 1032 198 921 137 275 1575 1102 1101 0\n1805 215 122 123 -723 0 1479 1478 784 1486 1488 1487 796 1485 798 786 776 793 785 1462 1461 1460 794 802 801 782 790 1651 1444 1443 1442 1796 1163 1030 245 326 1121 1789 1788 280 1756 1550 1549 1548 258 329 218 217 236 322 216 331 219 215 278 211 277 210 276 209 193 259 1153 266 1001 200 1088 1152 214 442 388 1020 733 559 1801 679 1556 406 351 1804 1781 1783 1799 1790 106 369 1087 1031 494 1093 108 110 1400 1797 461 541 1396 1394 160 1097 1591 389 397 1404 585 1764 926 147 148 378 72 363 1508 695 720 774 1414 119 546 435 577 1423 732 599 590 398 1331 1560 1275 1412 558 700 684 686 1273 557 560 1750 23 1420 594 21 387 752 505 553 350 1663 1659 1760 61 155 159 898 8 1684 1689 1325 0\n1806 -120 -829 -295 117 39 116 115 47 31 124 67 -187 68 122 770 123 0 801 776 782 546 398 393 910 416 1156 410 1152 352 1157 1740 442 388 0\n1807 95 223 124 29 -30 122 123 -723 0 1486 1487 1488 786 1480 1454 1455 1528 1456 793 1475 800 783 776 1485 796 785 1462 1461 1460 794 801 1465 1464 1463 1030 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1790 1088 1087 1093 461 389 279 214 200 105 369 494 1564 1514 345 225 566 97 1795 1135 679 1556 406 351 224 1796 1163 1788 280 1756 1550 1549 1548 218 245 326 217 236 322 216 331 219 1797 160 1097 585 1764 926 142 147 378 720 1414 546 1423 1331 1412 1806 173 593 950 746 1684 1334 1325 0\n1808 -95 124 -30 87 67 -187 352 58 59 122 56 123 -222 0 1488 1485 1487 796 1465 1464 1463 1492 1521 572 245 326 1121 1789 258 329 218 280 1781 910 173 938 129 1803 931 0\n1809 124 29 -30 87 122 123 -723 0 786 1630 1480 1475 783 776 793 1479 1478 784 1487 1488 1485 1486 796 1454 1455 1528 1456 785 800 797 782 777 794 790 1651 1444 1443 1442 802 105 369 453 1561 689 1788 1030 236 322 216 258 329 218 280 215 245 326 217 278 211 277 210 331 219 276 209 108 1397 494 1400 1394 1404 655 564 695 577 111 110 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1564 1514 345 225 566 97 1521 1257 1243 757 560 1795 1135 679 572 224 1756 1550 1549 1548 1049 1808 1807 347 1767 226 931 1803 176 393 935 524 1797 1436 1052 1632 1048 363 1508 1054 1056 435 617 725 168 172 1560 1275 553 755 684 685 1273 558 557 559 1750 1441 23 1427 594 1429 753 952 554 1659 155 0\n1810 29 -30 87 122 123 -723 0 786 1598 1630 1480 1475 800 783 776 1485 796 1456 1528 1455 1454 793 789 801 1030 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1564 1514 345 225 566 97 1521 1257 1243 1795 1135 679 1179 1171 572 1788 331 219 105 369 494 1809 134 397 485 541 503 379 371 455 386 1775 378 1250 0\n1811 -30 87 122 123 -723 0 786 1598 1480 1475 800 783 776 801 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1564 1514 345 225 566 97 1521 1795 1135 679 1179 1171 224 1788 1030 109 1810 106 1174 371 1808 541 397 0\n1812 -124 -389 166 -29 749 0 1488 789 801 198 275 1102 397 922 485 541 1105 1093 1101 1087 1576 1110 1533 936 143 1531 1092 0\n1813 -316 30 122 123 -723 0 786 1488 1475 800 783 776 1485 796 789 801 790 1030 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1790 1031 1032 138 1526 1529 1812 198 275 106 566 1564 1514 1795 1135 679 572 485 541 1010 371 704 1799 597 1767 0\n1814 95 30 122 123 -723 0 786 1598 1480 1488 1475 783 776 1485 796 800 797 790 1813 1030 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1790 1031 1032 138 1526 1529 1812 198 275 1102 137 106 1564 1514 345 225 566 97 1521 1795 1135 679 1179 1171 572 331 219 1799 1174 347 1767 370 1026 921 515 704 390 1109 1101 1575 1106 935 918 119 0\n1815 87 122 123 -723 0 1487 786 1480 1475 800 783 776 1485 796 1488 1465 1464 1463 1492 790 1030 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1790 1564 1514 345 225 566 97 1521 1795 1135 679 572 245 326 1121 1789 1788 218 1811 1031 1032 198 1526 137 138 1529 275 1102 1812 1814 1781 910 173 938 129 597 921 704 1575 1109 1101 0\n1816 30 122 123 -723 0 786 783 1480 1475 800 1487 796 1488 1492 790 1030 245 326 1121 1815 1786 176 1563 1805 242 342 1065 1064 1564 1514 345 225 1069 663 566 97 1521 1795 1135 679 572 1031 1032 1813 1814 198 137 397 938 275 129 1102 597 921 704 1575 1109 1101 0\n1817 -188 124 -30 120 67 96 352 58 59 122 123 240 0 931 1803 0\n1818 124 122 123 -723 0 1488 786 1480 1475 800 783 776 1485 1487 796 1492 1816 1030 245 326 1121 1815 1786 176 258 329 1211 1563 1805 242 342 1065 1064 1069 663 1554 403 350 1773 1564 1514 345 225 566 97 1521 1795 1135 679 572 224 280 1817 1767 129 938 1799 1807 1527 0\n1819 122 123 -723 0 1487 796 1475 800 786 1598 783 1480 789 1030 245 326 1121 1563 1805 242 345 1795 342 225 1135 1065 679 1064 1179 1069 1564 1171 663 1514 566 97 1521 1815 1786 176 1816 109 1818 397 485 379 1178 1599 386 377 476 0\n1820 132 4 89 68 153 0 1482 4 0\n1821 97 133 5 69 161 0 1494 6 0\n1822 185 121 57 0 1442 1443 1444 23 0\n1823 77 13 162 141 98 0 1495 29 0\n1824 186 80 122 144 58 0 1471 57 0\n1825 85 21 149 99 163 0 1493 69 0\n1826 187 59 123 88 152 0 1480 97 0\n1827 29 93 0 1454 1455 1528 1456 105 0\n1828 188 60 160 96 124 0 1492 129 0\n1829 38 102 166 0 1457 1458 1459 136 0\n1830 175 47 111 0 1460 1461 1462 160 0\n1831 184 120 56 0 1463 1464 1465 173 0\n1832 -205 197 0 1468 230 0\n1833 -213 197 0 1476 233 0\n1834 -214 198 0 1476 234 0\n1835 -221 197 0 1486 235 0\n1836 -222 198 0 1486 236 0\n1837 -198 -240 0 775 237 0\n1838 -199 -248 0 775 238 0\n1839 -213 205 0 1475 240 0\n1840 -214 206 0 1475 241 0\n1841 -215 207 0 1475 242 0\n1842 -221 205 0 1487 244 0\n1843 -222 206 0 1487 245 0\n1844 -205 -232 0 1469 249 0\n1845 -206 -233 0 778 250 0\n1846 -206 -240 0 1469 252 0\n1847 -207 -241 0 778 253 0\n1848 -207 -248 0 1469 255 0\n1849 -221 213 0 1485 257 0\n1850 -222 214 0 1485 258 0\n1851 -223 215 0 1485 259 0\n1852 -213 -232 0 1477 263 0\n1853 -214 -233 0 1470 264 0\n1854 -214 -234 0 781 265 0\n1855 -214 -240 0 1477 267 0\n1856 -215 -241 0 1470 268 0\n1857 -215 -242 0 781 269 0\n1858 -215 -248 0 1477 270 0\n1859 -221 -232 0 1488 275 0\n1860 -222 -233 0 1479 276 0\n1861 -222 -234 0 1478 277 0\n1862 -222 -235 0 784 278 0\n1863 -222 -240 0 1488 280 0\n1864 -223 -241 0 1479 281 0\n1865 -223 -242 0 1478 282 0\n1866 -223 -243 0 784 283 0\n1867 -223 -248 0 1488 285 0\n1868 -230 -234 0 1491 289 0\n1869 -230 -235 0 1489 290 0\n1870 -230 -236 0 788 291 0\n1871 -231 -241 0 1490 294 0\n1872 -231 -242 0 1491 295 0\n1873 -231 -243 0 1489 296 0\n1874 -231 -244 0 788 297 0\n1875 -232 -250 0 1491 298 0\n1876 -233 234 0 1468 299 0\n1877 -233 -197 0 792 300 0\n1878 -234 235 0 1475 301 0\n1879 -234 -205 0 792 302 0\n1880 -235 236 0 1485 303 0\n1881 -235 -213 0 792 304 0\n1882 -236 -221 0 792 306 0\n1883 -239 -245 0 792 311 0\n1884 -240 -253 0 792 317 0\n1885 -241 242 0 1468 318 0\n1886 -241 243 0 1476 319 0\n1887 -241 244 0 1486 320 0\n1888 -241 -198 0 796 322 0\n1889 -242 243 0 1475 323 0\n1890 -242 244 0 1487 324 0\n1891 -242 -206 0 796 326 0\n1892 -243 244 0 1485 327 0\n1893 -243 -214 0 796 329 0\n1894 -244 -222 0 796 331 0\n1895 -245 -230 0 796 332 0\n1896 -248 -254 0 796 337 0\n1897 -250 251 0 1475 339 0\n1898 -250 252 0 1487 340 0\n1899 -250 -207 0 800 342 0\n1900 -251 252 0 1485 343 0\n1901 -251 -215 0 800 345 0\n1902 -252 -223 0 800 347 0\n1903 -253 -231 0 800 348 0\n1904 -254 -239 0 800 349 0\n1905 -258 -272 0 776 401 0\n1906 -259 -280 0 776 403 0\n1907 -260 -288 0 776 406 0\n1908 -261 -296 0 776 411 0\n1909 -262 -304 0 776 414 0\n1910 -263 -312 0 776 416 0\n1911 -268 -281 0 779 417 0\n1912 -269 -289 0 779 419 0\n1913 -270 -297 0 779 423 0\n1914 -271 -305 0 779 427 0\n1915 -272 -313 0 779 428 0\n1916 -273 -258 0 782 431 0\n1917 -277 -290 0 782 435 0\n1918 -278 -298 0 782 439 0\n1919 -279 -306 0 782 442 0\n1920 -280 -314 0 782 446 0\n1921 -281 -259 0 785 450 0\n1922 -285 -291 0 785 453 0\n1923 -286 -299 0 785 457 0\n1924 -287 -307 0 785 461 0\n1925 -288 -315 0 785 463 0\n1926 -289 -260 0 789 466 0\n1927 -290 -268 0 789 468 0\n1928 -294 -300 0 789 474 0\n1929 -295 -308 0 789 480 0\n1930 -296 -316 0 789 485 0\n1931 -297 -261 0 793 486 0\n1932 -298 -269 0 793 488 0\n1933 -299 -277 0 793 491 0\n1934 -300 -285 0 793 494 0\n1935 -303 -309 0 793 498 0\n1936 -304 -317 0 793 504 0\n1937 -305 -262 0 797 506 0\n1938 -306 -270 0 797 509 0\n1939 -307 -278 0 797 511 0\n1940 -308 -286 0 797 515 0\n1941 -309 -294 0 797 518 0\n1942 -312 -318 0 797 524 0\n1943 -313 -263 0 801 529 0\n1944 -314 -271 0 801 534 0\n1945 -315 -279 0 801 537 0\n1946 -316 -287 0 801 541 0\n1947 -317 -295 0 801 546 0\n1948 -318 -303 0 801 549 0\n1949 -322 -336 0 777 602 0\n1950 -323 -344 0 777 605 0\n1951 -324 -352 0 777 608 0\n1952 -325 -360 0 777 613 0\n1953 -326 -368 0 777 617 0\n1954 -327 -376 0 777 622 0\n1955 -331 -337 0 780 623 0\n1956 -332 -345 0 780 625 0\n1957 -333 -353 0 780 629 0\n1958 -334 -361 0 780 634 0\n1959 -335 -369 0 780 638 0\n1960 -336 -377 0 780 641 0\n1961 -341 -354 0 783 649 0\n1962 -342 -362 0 783 654 0\n1963 -343 -370 0 783 658 0\n1964 -344 -378 0 783 663 0\n1965 -345 -323 0 786 667 0\n1966 -349 -355 0 786 671 0\n1967 -350 -363 0 786 672 0\n1968 -351 -371 0 786 676 0\n1969 -352 -379 0 786 679 0\n1970 -353 -324 0 790 681 0\n1971 -354 -332 0 790 684 0\n1972 -355 -340 0 790 689 0\n1973 -358 -364 0 790 695 0\n1974 -359 -372 0 790 700 0\n1975 -360 -380 0 790 704 0\n1976 -361 -325 0 794 707 0\n1977 -362 -333 0 794 709 0\n1978 -363 -341 0 794 712 0\n1979 -364 -349 0 794 716 0\n1980 -367 -373 0 794 720 0\n1981 -368 -381 0 794 725 0\n1982 -369 -326 0 798 729 0\n1983 -370 -334 0 798 733 0\n1984 -371 -342 0 798 736 0\n1985 -372 -350 0 798 737 0\n1986 -373 -358 0 798 740 0\n1987 -376 -382 0 798 747 0\n1988 -377 -327 0 802 753 0\n1989 -378 -335 0 802 757 0\n1990 -379 -343 0 802 761 0\n1991 -380 -351 0 802 764 0\n1992 -381 -359 0 802 769 0\n1993 -382 -367 0 802 774 0\n1994 29 93 0 1528 787 0\n1995 773 772 0 1598 1171 0\n1996 775 776 0 1605 1185 0\n1997 793 794 0 1630 1243 0\n1998 799 800 0 1651 1273 0\n1999 814 815 0 1691 1344 0\n2000 817 818 0 1710 1368 0\n2001 823 824 0 1712 1372 0\n2002 -772 120 -124 94 0 397 1930 379 130 1599 1178 377 386 476 0\n2003 120 -124 -30 88 152 151 56 123 51 0 133 111 109 1831 2002 1995 1179 1601 1969 571 1520 596 1968 1826 589 225 913 84 1901 193 0\n2004 -124 -30 -794 88 152 56 123 -222 0 1843 1891 1121 1789 1850 1893 218 1863 1049 133 397 932 2003 176 1268 1056 922 1048 1827 1051 369 503 1934 0\n2005 -120 124 825 158 94 280 152 343 123 -222 0 1245 1997 1554 366 1843 1891 1121 1789 1850 1893 218 176 393 1786 445 1001 1901 225 1826 596 1521 910 1969 1781 572 1179 1995 1174 369 1922 1934 1561 1400 1972 1394 664 1404 597 1973 655 1828 577 564 924 1646 0\n2006 -93 160 190 135 124 825 -122 343 151 235 0 395 1920 1554 1950 550 1245 1997 1944 1515 65 62 369 1516 1922 1934 375 1561 1374 1400 1972 2001 1394 664 1404 597 1973 655 577 564 1761 563 1961 1978 651 574 1560 1017 578 1927 467 473 424 1641 357 377 359 157 924 1752 1828 1999 1521 1355 1717 1960 553 594 682 1714 573 0\n2007 -149 231 13 -168 271 343 57 0 579 1952 552 563 1509 1961 651 574 1009 1947 421 358 1823 558 1499 1957 573 702 594 1822 394 834 527 1821 352 0\n2008 -168 93 160 -184 124 94 -122 343 123 -222 0 1994 198 593 1987 395 1920 366 1944 1515 1163 1843 1891 1121 1789 1863 1756 1550 1549 1548 1850 1893 579 866 1975 597 1767 274 2007 1761 80 564 1984 760 1021 596 1924 1826 371 225 913 898 1159 1901 1152 1153 0\n2009 -342 93 -184 123 -723 0 593 1987 1819 395 1920 366 1515 1030 1843 1891 1121 1789 1850 1893 218 1984 760 1021 596 1924 1826 371 225 913 1900 1901 1902 193 1799 1783 0\n2010 160 -30 123 -723 0 1788 1030 1796 1819 1515 395 1920 109 111 1836 1888 216 1850 1893 218 1863 215 1843 1891 217 1862 211 1861 210 1894 219 1860 209 108 1397 366 1245 1997 2004 2005 1831 593 1987 599 1954 554 1121 1789 2006 1994 1526 1530 2008 2009 564 1761 1641 563 578 651 0\n2011 -30 123 -723 0 1819 395 1920 1245 1997 366 1515 59 1796 1030 1843 1891 1121 1789 1788 1850 1893 218 217 1836 1888 216 1894 219 1863 215 1862 211 1861 210 1860 209 108 109 111 1397 2004 2005 1831 2010 572 1969 596 1826 225 913 1900 1901 1902 193 200 1088 1781 1783 1790 1799 1087 1093 1798 1924 84 389 0\n2012 -59 123 -723 0 2011 1031 1526 1032 1529 1532 1819 395 1920 1796 1030 1843 1891 1121 1789 1788 1850 1893 218 225 1900 1901 1902 193 266 1001 214 445 1830 393 1831 913 1781 1783 1776 0\n2013 -184 124 123 -723 0 1819 1515 395 1920 366 2012 1826 596 1969 572 1521 2011 1031 1526 1032 1529 106 1554 1950 550 593 1533 678 1531 571 1779 1767 1828 1799 938 0\n2014 124 123 -723 0 1819 1515 395 1920 366 2012 1826 596 1969 1179 1995 572 1521 2011 1031 106 1554 1950 550 1030 1843 1891 1121 1789 1788 1850 1893 218 1894 219 2013 799 1786 910 1781 1783 1174 1799 370 1767 1940 1779 935 390 927 119 0\n2015 123 -723 0 1819 395 1515 1920 366 2011 1031 1032 198 1526 138 1529 1859 1102 2012 1826 596 1969 2014 397 922 1812 1930 1098 1105 678 1101 593 1576 0\n2016 -124 166 -29 184 0 198 1859 1102 397 922 1930 1576 1105 1101 0\n2017 -60 30 184 -723 0 1031 1526 1032 1529 1532 2015 396 1925 1030 1894 226 1902 335 279 222 214 799 1830 393 940 1776 462 371 0\n2018 30 184 -723 0 2015 396 1925 1173 1995 372 1522 1031 1032 138 2016 2017 1828 597 1778 1975 1603 579 0\n2019 184 -723 0 2015 396 1925 1173 1995 372 1522 1030 1894 2018 111 1766 1602 571 591 1968 1991 1986 739 597 577 1561 1922 369 1994 2016 1828 226 940 335 1831 222 0\n2020 -151 -723 0 2019 176 1030 1843 1891 1121 565 1513 1963 1577 1127 1120 0\n2021 -723 0 1030 1850 1893 218 2015 396 1522 1925 1945 372 365 2019 911 2020 1783 1781 1766 1790 111 1778 1031 1032 106 1526 138 1529 1799 1812 1902 1828 226 0\n2022 -158 -29 747 96 188 95 159 0 198 1882 1395 1526 106 115 118 570 1174 1777 1094 1985 1995 1087 590 1179 1574 1951 1532 551 1765 1737 377 1394 1928 1400 0\n2023 -29 747 96 188 131 135 143 187 95 159 0 2021 106 198 1849 1881 1296 2022 1562 1573 1029 1087 1033 1034 1572 1923 1517 163 1298 1679 1295 0\n2024 158 166 180 -93 747 31 160 769 379 23 51 87 151 159 0 2021 1781 1562 1573 1601 1029 1087 1995 1033 1093 1173 1940 1924 1925 390 389 1025 119 84 1901 920 589 1153 1984 1152 564 1166 0\n2025 363 180 -93 747 31 131 135 143 187 95 159 0 369 1922 1374 2001 1934 1516 582 1727 589 1968 718 1098 585 1087 1726 148 920 1097 119 385 390 497 0\n2026 96 188 160 124 327 769 143 -343 23 51 87 151 159 0 2021 604 550 554 1990 596 1781 1828 226 1902 200 1088 2023 1827 369 1516 1922 1561 1374 1972 2001 659 590 2025 1967 570 1036 2024 1029 139 1033 1035 1940 1517 390 119 920 928 1726 0\n2027 -93 -770 747 31 327 143 -343 95 151 159 0 604 550 554 1990 596 369 1516 1922 1561 1374 1972 2001 659 590 2025 1978 563 1593 83 564 1727 1984 589 0\n2028 -363 93 -770 747 95 151 159 0 1967 1978 570 563 1573 1596 1087 163 1572 0\n2029 171 180 -827 86 22 132 179 107 172 43 188 -376 -343 0 1954 604 550 1963 743 595 1990 596 588 75 1732 564 581 1962 0\n2030 188 160 124 -376 769 143 -343 23 51 87 151 159 0 2021 1954 1990 1781 2026 372 1925 1025 1900 1901 1902 1153 200 1088 1152 2027 1994 198 1526 1849 1882 1881 1395 211 2028 1017 1923 370 1033 1094 1029 1087 1036 1562 1098 1574 118 1518 1968 607 1532 589 551 1765 84 377 389 901 1928 1939 1400 364 1394 582 1985 2029 590 0\n2031 160 124 -376 769 143 -343 23 51 87 151 159 0 2021 661 1987 1990 1781 2030 597 1975 763 692 570 1036 1561 1601 1029 1922 1995 1033 369 1173 1923 1994 1925 198 1025 1849 1900 1901 1881 1902 1153 1017 1088 1152 2028 0\n2032 -223 123 187 0 1851 1794 1901 1067 1563 225 1920 1515 1826 366 0\n2033 -160 327 769 143 -343 95 151 159 0 604 550 554 1990 1135 596 131 135 1522 2032 200 1088 2023 1827 2027 1152 1153 1901 1795 225 1067 1563 1920 1515 366 1826 0\n2034 -93 -350 30 31 131 135 143 187 95 159 0 1985 590 1967 106 2025 1089 0\n2035 -158 30 31 -124 131 135 390 143 187 95 159 0 397 1930 1105 134 130 570 2034 1994 198 1526 2022 922 1859 1530 1102 1101 1110 143 1092 1090 1531 1529 0\n2036 158 748 187 159 0 1766 1573 2032 1087 1088 0\n2037 -184 769 143 -343 23 51 87 151 159 0 1990 596 1781 593 1533 1954 554 604 550 2033 2031 397 936 1946 1093 2036 111 2035 0\n2038 -124 254 223 187 23 51 87 151 159 0 1088 1781 130 134 397 1946 1093 1005 2036 1087 1968 570 2022 1574 589 1967 1827 585 84 582 369 1516 1993 389 1922 1028 1939 1374 449 2001 1554 1727 1950 550 0\n2039 -749 -280 254 23 51 87 151 159 0 1098 1574 1968 585 589 1993 84 1028 389 449 1939 0\n2040 -158 -371 -748 185 -770 -56 95 151 159 0 1544 115 570 1967 1094 1534 1547 1546 1545 1822 718 585 1170 148 1095 1097 1535 971 1536 969 0\n2041 -323 -770 -56 379 23 51 87 151 159 0 222 1867 1088 200 1896 1781 1950 749 1554 594 2039 1087 1093 1924 389 84 589 1984 564 1792 1593 1869 1880 563 206 1882 650 577 2040 198 1166 1829 1827 578 920 377 369 1974 1941 590 514 119 390 0\n2042 -748 323 -770 747 31 143 -343 23 51 87 151 159 0 1781 1093 1924 389 84 589 1984 619 1792 2027 1880 1994 1882 198 0\n2043 -29 -318 188 -158 747 95 159 0 570 1967 198 2022 1849 372 1881 1925 1017 548 0\n2044 -343 756 23 51 87 151 120 159 0 1781 1963 1990 1127 596 1120 1124 1577 1919 54 1157 2037 1831 222 1858 1867 1896 1153 200 1088 1152 2041 550 2042 2036 1087 570 1098 1574 1967 1968 1991 585 582 589 597 1993 1028 2043 1827 369 1516 1922 1727 1374 2001 0\n2045 135 -779 -86 117 175 93 -772 123 120 0 1510 1616 1614 595 1514 170 908 1964 1600 566 1521 1826 0\n2046 -29 -772 107 123 -179 -748 756 95 120 0 589 1984 564 106 198 1094 1572 1835 1842 1849 1517 163 385 900 1877 1879 1881 1935 1948 210 1196 211 391 75 364 1510 1918 381 1198 495 1195 1124 1120 1127 1983 559 2045 554 1954 1988 593 1831 1579 222 869 1896 37 1028 359 770 1913 1015 0\n2047 -135 57 120 0 18 21 22 554 1059 1061 1954 1057 593 1063 0\n2048 -306 149 298 -93 -179 -748 95 0 369 1922 375 1516 1919 495 385 1097 378 893 437 1825 363 0\n2049 -122 175 171 -56 163 167 159 0 222 1848 1233 395 883 1944 1629 1236 1232 0\n2050 -168 160 96 124 -93 0 579 924 1975 1828 597 0\n2051 -166 -170 -175 -85 -93 317 0 581 1962 1084 1510 40 585 1993 162 369 1934 1400 139 577 917 892 1568 1973 768 1078 1404 1027 1079 1394 1884 1853 215 209 1396 0\n2052 -170 -175 -85 168 -93 -103 0 585 1980 1423 378 363 1917 478 388 1947 535 396 374 1508 369 1922 479 389 1374 2001 539 397 1516 398 1929 390 148 147 581 1977 558 2051 1377 1110 9 1498 1823 184 855 1844 791 1102 206 1101 1895 1105 1413 1908 483 1412 404 402 395 351 350 1740 0\n2053 166 -175 -85 168 -93 -103 0 2052 585 1993 363 1917 1560 1971 557 1275 1998 374 1508 1552 1550 1549 1548 369 1922 1374 2001 1516 148 1377 573 1498 1957 558 1823 861 1666 595 1989 756 560 559 1750 1822 594 1988 752 554 553 1659 0\n2054 -205 48 -825 43 44 47 0 1832 1879 1877 210 209 1396 0\n2055 -333 381 170 373 -85 0 363 1917 1275 1998 1508 755 732 595 588 1666 0\n2056 -175 -85 168 -93 -103 0 363 1917 374 1508 70 1552 1550 1549 1548 369 1934 1400 106 378 1947 1331 162 163 585 1980 1993 2052 2053 577 917 892 1973 768 1404 1334 1027 1394 1325 1884 215 1049 2054 184 1686 948 1052 1048 1054 1953 611 552 2055 558 995 1823 1912 1498 858 373 1396 209 829 1877 1821 178 0\n2057 358 141 -103 168 -85 -93 0 148 363 1917 1275 1998 374 1508 1552 1550 1549 1548 369 1922 1374 2001 1516 577 1377 573 1498 682 1823 553 861 1659 1661 2047 176 0\n2058 166 184 -103 168 -85 -93 0 148 363 1917 1275 1998 374 1508 369 1922 1374 2001 1934 1516 1377 573 1498 1957 558 2057 1823 1973 861 1018 1661 1870 553 206 1953 1829 586 855 1662 0\n2059 -13 170 -825 43 44 184 -103 168 -85 0 363 1917 378 478 1124 1275 1998 1508 184 861 1879 1579 1662 1120 166 1121 2054 309 214 0\n2060 178 170 364 44 102 184 -295 168 -85 -93 0 583 363 1947 535 396 369 539 1223 1917 478 1124 1275 1998 1508 1552 1550 1549 1548 1934 383 1579 1666 1662 1120 61 595 1514 586 1121 1964 724 657 1889 1890 566 1225 1084 1893 1894 1220 1079 199 1078 1568 908 1826 1222 596 933 1969 107 674 570 0\n2061 170 141 184 -103 168 175 -85 -93 0 369 1934 1400 2058 577 1973 1404 1394 1986 1423 892 917 139 363 378 1947 535 396 539 397 1917 478 388 1922 479 389 398 1929 390 148 147 1560 1971 557 1275 1998 374 1508 1552 1550 1549 1548 2059 1823 358 1498 858 1912 532 373 477 395 387 2060 56 588 1983 559 1750 1822 1420 594 1412 1988 1413 554 1883 1660 214 166 586 1396 1953 209 829 611 1877 552 178 1821 0\n2062 141 -382 -103 168 175 -85 -93 0 369 1934 1400 1987 593 2058 577 1973 1404 1394 1986 1423 892 917 139 1993 363 378 1947 535 396 539 397 1917 478 1124 388 1922 479 389 398 1929 390 147 1560 1971 557 374 1508 2061 40 45 581 1510 1962 710 1568 1084 666 560 1078 1554 1750 1079 1920 1840 1853 1855 395 1891 209 215 1121 1396 1120 214 1579 1883 861 1413 1823 1412 358 1420 1912 387 477 0\n2063 -382 -103 168 175 -85 -93 0 378 1987 593 2058 139 577 917 1973 1986 2062 558 1977 732 581 588 2060 0\n2064 184 170 -103 168 -85 -93 0 2056 2063 2058 2061 577 558 1986 768 2055 0\n2065 170 -103 168 -85 -93 0 378 1947 1331 2056 148 363 1917 1275 1998 1508 70 1552 1550 1549 1548 106 2064 176 950 2047 1664 1660 61 586 1685 1981 1325 1334 0\n2066 61 48 38 -807 -825 -170 -103 -85 -93 0 363 1917 378 478 1124 70 1552 1550 1549 1548 106 1685 1686 61 184 861 855 1580 1879 791 1120 917 892 1121 2054 309 214 0\n2067 -103 168 -85 -93 0 363 1917 1560 1971 557 72 369 1934 1400 378 2056 1947 478 2063 398 1331 539 535 1124 1439 397 396 2065 40 45 581 1510 1962 1977 564 1084 558 2057 1973 768 1404 1018 1334 1027 1394 1870 1325 1884 206 215 1049 2066 950 2058 139 917 892 948 1568 1078 1079 1840 1853 1891 209 1121 1396 1789 1120 161 214 1761 1579 1052 1904 56 1048 1428 1750 1056 1427 171 1437 0\n2068 -166 -253 -170 103 -85 -93 0 1903 1039 1884 215 581 1962 1084 1510 40 369 1934 1400 139 577 917 892 1568 1043 1973 1078 1038 1404 1079 1394 1834 1840 1853 1893 1888 1891 209 218 216 217 1396 162 214 1047 312 920 222 1397 0\n2069 102 -61 752 166 48 231 103 0 154 153 207 791 1106 206 1101 292 1104 214 0\n2070 -61 -253 184 -170 168 -85 -93 0 2067 2068 1576 1903 207 1884 1049 215 581 1977 558 363 1917 374 1508 1552 1550 1549 1548 369 153 2069 137 855 946 1103 1823 1056 1101 358 1498 1048 1105 1912 1770 1051 1908 482 952 1909 352 404 402 394 1831 353 351 350 1822 222 843 594 1838 1690 1988 1338 1343 1337 0\n2071 -253 805 49 50 51 245 727 166 -93 0 1903 336 1039 222 1038 1045 1046 1974 920 1323 1318 1316 0\n2072 -728 58 253 805 -94 49 50 729 243 166 -93 0 218 1552 1550 1549 1548 1045 1046 1974 1992 920 1323 1027 1316 1936 1318 1051 175 222 1048 334 1056 225 933 1319 0\n2073 102 166 -170 168 -85 -93 0 2021 581 1977 558 1962 1084 564 1510 2067 363 1917 374 1933 1508 72 369 1922 1561 1972 791 1568 1043 206 857 1078 1869 1895 1823 1079 1017 184 1834 1855 1893 1967 1844 325 1888 1049 218 1036 1102 217 216 1029 1033 1035 1940 1320 2071 341 224 1065 2072 1038 1039 1874 1022 1974 659 578 565 1110 1761 1101 1563 1106 1064 865 1564 0\n2074 49 61 189 181 53 13 -102 141 -85 -93 0 377 363 1917 374 1508 1823 358 1912 471 1116 1941 1418 72 70 1552 1550 1549 1548 106 1738 1412 1742 552 830 1976 1115 1118 1113 0\n2075 253 13 -102 166 141 168 -85 -93 0 1508 363 1917 374 1823 1498 1770 578 1992 598 377 358 1912 471 380 1187 1996 151 146 373 227 1027 1947 475 385 2074 19 216 832 1606 1888 593 179 1954 1987 612 599 552 1608 1821 594 178 827 752 1877 553 209 308 10 214 837 1830 0\n2076 -49 754 105 -776 97 -167 161 13 -102 166 14 168 21 -93 0 369 377 1941 514 578 1974 1022 1894 199 1552 1550 1549 1548 106 19 216 832 1606 1886 1888 593 1893 179 1954 1987 192 612 599 1439 552 1608 1821 594 178 827 752 1877 553 209 1114 308 10 1113 214 837 1119 795 168 946 385 1743 1948 1427 1436 0\n2077 166 -170 168 -85 -93 0 581 1977 558 39 363 1917 374 1508 70 369 2073 377 855 1941 1823 514 358 1498 1320 1912 1770 373 1187 471 146 151 578 920 864 894 1996 380 1116 1974 1992 1323 598 1316 2075 2076 1318 2074 175 2070 0\n2078 -170 168 -85 -93 0 2067 369 1934 1400 40 581 1510 1962 1084 2077 139 577 917 892 1568 1973 1986 1078 1404 591 1079 1394 1834 1840 1853 1855 1893 1888 1891 209 215 218 216 217 1396 214 943 1883 312 220 222 1397 219 920 1874 140 207 0\n2079 48 41 141 47 -825 44 -166 -85 0 892 363 1917 374 1508 1396 2054 858 184 1823 0\n2080 -48 278 171 179 382 30 38 -93 0 1439 369 1922 1374 2001 1516 164 215 1837 1846 1855 179 185 192 1000 1435 760 1427 596 1436 1727 449 550 1554 1950 0\n2081 -52 111 780 53 -166 167 102 168 -85 -93 0 369 1934 1400 577 1973 1404 1394 1986 591 892 917 138 2067 1043 2078 363 1917 374 1508 106 120 123 124 219 1097 1874 1894 207 1039 199 140 1038 1089 943 1045 1047 1087 1992 585 1098 1573 2055 1993 1968 570 558 589 1217 1967 1210 582 1214 1939 364 2080 2054 2079 184 995 11 12 13 209 829 824 1823 1912 1624 1845 1853 1877 1498 373 1187 185 192 178 1996 1228 1821 1227 552 1231 1952 728 1953 701 587 586 593 1192 0\n2082 -367 5 205 69 169 -358 170 168 -85 0 184 1986 363 1917 374 1508 1993 696 768 2055 558 995 1823 1912 1498 373 1187 1821 1996 552 1952 728 697 701 587 586 593 1192 0\n2083 -77 175 5 69 169 -358 167 170 168 -85 0 363 1917 1275 1998 1508 358 1498 1912 1285 373 586 1821 1953 552 611 0\n2084 -41 -166 167 170 168 -85 0 577 1986 363 1917 1275 1998 374 1508 13 209 829 1876 1877 1879 178 184 2082 585 2083 1823 558 1957 2055 573 1981 1285 586 0\n2085 -333 373 170 168 -85 0 363 1917 1275 1998 1508 732 2055 588 1981 746 586 593 1662 0\n2086 -135 176 141 170 168 -85 57 0 363 1917 1560 1971 557 1275 1998 1508 554 2047 1988 176 594 1662 1822 56 588 1750 1983 559 0\n2087 -175 804 780 141 41 -166 -85 -93 0 369 1934 1400 577 1973 1404 1394 917 138 162 585 2079 1993 719 215 1323 1863 1316 199 1320 1940 1004 1967 582 718 589 1217 2080 1210 1939 1214 0\n2088 176 175 141 167 170 168 -85 57 0 363 1917 1275 1998 1508 2086 1660 0\n2089 -42 141 -166 -85 0 363 1917 374 1508 210 858 1879 1823 184 0\n2090 48 50 51 53 141 41 -825 44 -166 49 167 103 -85 57 0 2089 577 1986 591 892 2079 943 140 207 1872 1873 1874 219 1397 222 335 333 334 226 224 225 1399 0\n2091 -56 111 176 170 103 168 -85 108 0 363 1917 1275 1998 1508 175 222 1662 1858 588 1512 1153 1963 1592 1152 1163 0\n2092 50 51 53 -166 49 167 102 168 -85 -93 0 2078 577 1986 2085 558 2084 369 1934 1400 1973 1404 1394 917 2067 1552 1550 1549 1548 383 2090 166 2088 163 2091 1212 2081 2087 1318 0\n2093 -50 53 42 181 38 167 727 170 103 -85 0 363 1917 1275 1998 1508 47 51 217 1666 1857 1865 1872 1889 1890 1891 595 193 200 207 1039 1893 1894 185 1989 140 1038 192 199 1240 391 1047 1234 1232 1935 585 872 1236 636 489 559 381 37 0\n2094 53 -166 49 167 102 168 -85 -93 0 2078 577 1986 2085 558 2089 2084 369 1934 1400 1973 1404 1394 591 917 138 2067 1043 363 1917 1275 1998 1508 70 383 106 2093 2092 85 89 218 1866 1873 1892 1893 200 207 1039 1894 192 140 1038 199 943 1047 1154 2079 163 166 1592 1152 1163 1963 588 1666 1662 595 593 743 0\n2095 -166 49 167 102 168 -85 -93 0 2067 1043 2078 363 1917 1560 1971 557 1552 1550 1549 1548 1768 369 1934 1400 383 138 577 1542 917 1973 1986 1540 1404 1394 2084 2085 558 2094 141 220 944 1040 1883 1038 214 1047 2079 585 1537 164 166 215 1993 2086 2091 1837 1846 1855 1863 1439 179 185 192 199 1435 1427 1436 1942 393 1831 593 1538 1954 1539 616 1822 994 394 842 1937 1915 1943 387 1346 354 16 1999 1751 587 1699 1959 559 636 0\n2096 166 167 102 168 -85 -93 0 2021 2067 1043 363 1917 1275 1998 1933 1508 369 1922 1374 2001 1934 1516 791 1046 1377 206 1038 573 1869 1870 1039 1970 1017 1018 1874 1967 615 1036 553 1029 1659 1033 554 1940 620 1022 0\n2097 167 102 168 -85 -93 0 2067 1043 2078 1552 1550 1549 1548 369 1934 1400 383 2096 138 577 1542 917 2084 2095 1973 1986 1540 17 216 1404 2085 1847 1856 1864 1871 1885 1886 1887 1888 1394 558 186 193 200 207 1039 1891 1893 1894 179 1038 185 192 199 1047 1339 162 163 585 1537 2079 1993 164 166 1439 1435 2091 1427 1436 1942 393 1831 593 1538 1954 1539 1343 1822 1337 394 1341 1943 0\n2098 -175 610 120 69 -825 44 -166 170 103 168 -85 108 0 577 1986 2085 558 892 162 163 585 1537 1538 799 2091 166 2079 2054 13 209 2082 1877 178 0\n2099 47 48 133 69 -825 333 44 -166 -85 0 558 892 363 1917 374 1508 2079 2054 209 184 995 1877 1823 1912 178 1498 373 1821 0\n2100 245 133 69 -241 333 -85 0 1885 558 363 1917 374 1508 321 325 178 184 995 1823 1912 1498 373 1821 0\n2101 327 -49 -166 -167 168 -85 -93 0 216 1864 200 138 1856 193 1847 186 143 17 1885 1891 185 1888 179 1887 1894 199 1886 1893 192 1339 832 369 1934 1400 577 1973 1404 1394 2078 1986 2085 1542 1540 917 578 1974 590 894 920 2067 363 1917 1275 1998 1508 1552 1550 1549 1548 383 1343 612 1337 552 1341 1910 1943 393 394 1822 1539 2098 2100 1883 214 1830 2099 385 164 166 1948 497 1435 1436 390 1427 1439 1987 593 1662 588 1512 1963 565 1783 1781 119 0\n2102 -49 -166 -167 168 -85 -93 0 369 1934 1400 577 1973 1404 1394 2078 1986 2085 917 363 1917 1275 1998 1560 1508 1552 1550 1549 1548 216 832 2101 1954 1988 593 594 1822 394 1915 1553 1949 734 609 588 552 1662 2100 166 1883 2099 214 0\n2103 -178 215 31 38 180 51 52 103 108 0 1153 193 588 1512 1963 565 1163 1783 1781 1152 119 1592 390 385 1772 0\n2104 178 831 -48 42 170 168 -85 0 215 1846 185 166 363 1917 1275 1998 1508 1666 1662 595 877 593 1964 1987 1554 1439 756 1920 1427 559 1436 37 547 381 0\n2105 239 69 133 49 -825 -236 44 -166 806 180 51 52 170 103 168 -85 108 0 577 1986 2085 558 2089 138 363 1933 214 307 2099 200 164 215 1837 1846 1855 1863 179 185 192 199 1435 2104 51 2103 1858 305 222 1017 1318 1967 1316 1004 1320 1940 0\n2106 -178 111 69 -166 102 168 -85 -93 0 2021 2097 2102 2078 577 1986 2085 558 2089 892 578 1974 1323 894 920 2067 363 1933 1298 1552 1550 1549 1548 369 1934 383 1922 375 51 588 1512 1963 1983 1592 1163 1151 1152 1153 1841 1858 1901 1899 222 225 224 1318 1316 1320 1940 370 1033 1029 1036 1967 1306 1295 1297 13 209 1845 1876 1877 1146 1879 178 1145 2082 1588 585 871 1830 0\n2107 -215 67 48 69 764 49 42 -825 172 43 44 806 51 52 108 0 1857 1858 217 222 1318 1397 1316 209 1320 1860 1877 1940 199 1139 370 107 1138 824 1584 0\n2108 -50 245 141 -167 -85 0 363 1917 374 1508 217 864 325 1823 184 0\n2109 -758 50 215 152 88 178 111 254 49 806 51 52 103 108 0 1153 1127 1579 1963 175 593 1163 1001 1318 1987 1152 1945 1316 1028 1592 396 1320 1942 913 1826 516 596 1556 1969 0\n2110 69 325 -166 102 168 -85 -93 0 1144 552 2097 2102 2078 577 1986 2085 558 2089 369 1934 1400 1973 1404 1394 1018 583 892 917 578 1974 1323 590 894 920 2067 363 1917 1275 1998 1508 72 1552 1550 1549 1548 383 2105 1883 1904 1023 1428 1935 385 2106 1666 2104 61 65 595 1514 2099 1964 162 566 1554 1906 350 2107 1153 2108 1123 2109 1120 1124 1578 1919 1513 1157 1595 1152 0\n2111 48 756 50 -186 -69 49 -825 44 -166 51 52 170 103 168 -85 108 0 595 1964 1257 1997 1514 352 1908 379 829 577 1986 2085 558 2089 892 2079 1397 161 175 2091 1786 170 1634 0\n2112 -48 40 104 -166 189 168 0 215 947 1884 152 227 0\n2113 -186 -69 -166 -167 168 -85 -93 0 352 1931 1116 1552 1550 1549 1548 2102 829 1115 1113 1118 1958 559 1908 379 2078 577 1986 2085 558 369 1934 1400 1973 1404 1394 917 578 1992 598 894 920 2067 363 1917 1560 1971 557 383 61 595 1989 560 1750 1822 835 2112 2079 214 1883 2108 1123 2111 0\n2114 -69 -166 -167 168 -85 -93 0 2102 2078 577 1986 2085 558 2089 369 1934 1400 1973 1404 1394 892 917 578 1992 598 894 920 2067 363 1917 1560 1971 557 1275 1998 1508 1552 1550 1549 1548 383 352 829 1908 1931 1115 379 1116 1113 1118 1958 559 2113 1666 51 56 588 1512 1750 1963 1822 1163 835 2112 2079 1397 161 222 1592 1858 1152 1153 0\n2115 -325 381 -354 57 0 1952 751 687 594 1553 1822 1915 394 0\n2116 -166 102 168 -85 -93 0 1552 1550 1549 1548 363 1917 1560 2097 578 1992 2115 2114 2110 0\n2117 185 69 102 168 -85 -93 0 2021 2097 578 1974 1323 363 1933 2116 791 206 1869 1017 1967 1036 1029 1033 1940 1320 1316 1917 1560 1971 369 1934 1870 1018 635 1151 559 1922 1561 1972 655 564 1400 1395 1394 1895 916 1552 1550 1549 1548 1992 2115 1144 1334 590 894 920 2067 1043 557 72 1768 375 1516 1822 394 1915 1553 1346 643 1999 597 1737 5 551 1951 1970 727 646 1556 1559 587 561 1925 418 1912 465 1735 396 357 358 350 1500 1587 1585 1145 1138 1146 1139 1891 321 217 1121 216 2071 1318 1789 1326 175 222 951 1761 1325 1706 1707 1786 1867 1896 1687 88 104 939 2038 0\n2118 50 49 313 -804 805 116 -827 245 172 166 180 381 51 52 727 140 -93 0 2071 1318 1027 222 542 1867 1559 200 1970 551 1737 597 937 1991 119 571 0\n2119 -50 245 -167 170 -85 0 578 1992 363 1917 1275 1998 1508 51 2108 1666 558 595 755 0\n2120 69 102 168 -85 -93 0 2021 2078 2097 2116 791 206 1895 2119 578 1974 1323 363 1933 1869 1017 1967 1036 1029 1033 1940 1320 1316 390 369 1922 1561 1972 1934 1870 1018 655 1400 1395 1394 1868 916 1552 1550 1549 1548 1917 1560 1992 2115 552 590 894 920 2067 1043 1971 557 2117 594 1960 1553 1915 2118 216 1886 2100 1893 1977 1000 1016 1918 0\n2121 102 168 -85 -93 0 2021 2078 2067 363 1917 1560 1971 557 1933 369 1934 1400 1043 2097 578 920 894 1974 1992 590 1323 598 2116 791 206 916 1869 1870 1895 1017 1395 1967 1394 1036 1029 1033 1940 1320 1316 2119 2120 7 352 832 1908 2071 1318 379 227 951 1188 152 1996 923 1189 1737 1970 551 0\n2122 -56 180 343 50 49 52 51 168 -85 -93 0 2121 137 2078 2067 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1934 383 175 222 1858 1867 1001 200 1919 2103 1124 1666 1579 61 1120 1123 0\n2123 359 358 168 -85 -93 0 2121 139 363 1917 1275 1998 1508 369 1922 1374 2001 1516 578 1377 573 682 683 553 554 1659 0\n2124 -373 50 49 52 51 168 -85 -93 0 369 2121 377 1941 514 1320 363 1917 1560 1961 1986 660 2123 1974 590 1323 2122 1316 1318 0\n2125 372 50 49 52 51 168 -85 -93 0 369 2121 377 1941 514 1320 139 2078 363 1917 1275 1998 1508 590 1323 1316 1318 175 2122 1963 588 1661 1662 553 586 1953 0\n2126 50 49 52 51 168 -85 -93 0 2121 139 2078 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1922 1374 2001 1516 2124 2085 558 2125 1974 578 2123 1377 696 573 585 683 2088 554 586 1659 1953 553 0\n2127 49 52 51 168 -85 -93 0 369 2121 377 1941 514 390 363 1917 472 1198 381 139 137 2078 1275 1998 374 1508 1552 1550 1549 1548 1934 383 1059 2126 47 51 217 1666 1857 1865 1872 1889 1890 1891 595 1514 193 200 207 1893 1894 185 1964 1989 192 199 1234 1257 1240 1232 1997 1236 1914 1060 1057 1062 1982 553 1661 176 593 2047 1987 1659 756 578 864 559 632 558 1823 184 865 1879 1639 210 1196 170 37 1195 1500 872 1205 0\n2128 -376 369 810 57 0 1954 742 1343 594 1337 1822 1341 394 1943 0\n2129 -326 52 51 168 -85 -93 0 2127 216 1864 200 2121 137 1856 193 1847 186 1871 207 17 1885 1891 185 1888 179 1887 1894 199 1886 1893 192 1339 1153 18 2078 2067 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1934 383 1953 1982 586 2128 593 1662 588 1512 2103 1963 590 1163 1974 1152 578 1592 1660 163 0\n2130 52 51 168 -85 -93 0 369 2121 377 1941 514 390 1418 139 137 2078 2067 363 1917 1560 1971 557 1275 1998 1508 72 70 1552 1550 1549 1548 1934 383 106 2127 18 216 1856 1864 1888 200 2129 553 994 1659 1909 146 151 578 386 1974 1992 590 598 2115 2103 552 1666 1661 595 1514 176 593 1964 1989 755 1987 1257 560 558 756 1997 1742 559 1639 1412 1750 154 865 1822 1417 833 0\n2131 -52 168 -85 -93 0 1534 2121 1535 139 2078 2067 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1922 1374 2001 1516 219 920 1874 1046 1377 1039 1038 573 1044 1957 163 1536 558 970 2088 2047 586 1659 1953 553 0\n2132 168 -85 -93 0 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1922 1374 2001 1534 1516 2067 2078 2121 139 1535 2131 2130 218 894 1873 1046 1377 1039 1038 573 1044 1957 163 1536 558 970 2088 2047 586 1659 1953 553 0\n2133 -727 103 135 170 167 -85 -93 0 2132 579 1975 1225 924 898 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1042 1044 1947 163 539 1664 1223 61 1220 1222 0\n2134 103 135 170 -51 326 -85 -93 0 218 1866 200 106 85 70 1893 192 1892 1894 199 1154 1079 1873 1039 894 91 90 89 72 369 1922 1374 2001 1934 383 1516 2133 1038 1046 1047 139 163 903 1592 1568 1152 1078 1163 1593 1084 1990 83 603 596 550 1727 0\n2135 135 170 -51 326 -85 -93 0 894 2132 579 1975 1225 924 898 363 1917 1275 1998 374 1508 1552 1550 1549 1548 369 2134 378 1947 539 1223 1220 1222 61 867 1664 1666 585 588 861 1980 1823 732 558 0\n2136 170 -51 326 -85 -93 0 218 1873 207 1866 200 89 85 2132 579 1975 1225 924 898 157 363 1917 1275 1998 1508 1552 1550 1549 1548 369 1934 383 2135 18 22 554 2047 1059 1954 1988 176 393 594 1063 1822 1057 394 1060 1915 1914 1553 1236 734 588 1666 61 595 1514 880 1222 1964 1989 1220 1257 1240 1223 1997 1232 1930 503 1235 481 386 161 378 1634 0\n2137 -51 326 -85 -93 0 2132 579 1952 552 159 155 72 70 1552 1550 1549 1548 106 218 894 1873 1893 1039 1079 2136 581 1510 1962 1977 1084 558 1078 1689 1568 139 855 1046 1686 1038 1325 1042 1331 1947 0\n2138 -295 -170 -85 -93 0 72 2132 159 579 1952 552 581 1977 558 1689 1962 1084 564 1510 155 363 1917 70 1552 1550 1549 1548 106 1947 478 1331 535 1124 1325 396 1686 1685 855 61 224 1568 1897 1078 1901 1079 1153 1840 1891 1121 1789 1120 1593 1580 1152 1512 861 1590 0\n2139 166 -167 50 49 102 -205 727 51 -85 -93 0 2021 578 1974 1323 920 2132 924 898 363 1933 1552 1550 1549 1548 791 206 1869 1895 1017 1967 1036 1029 1033 1940 1320 1316 2071 1319 341 224 0\n2140 -167 -13 -170 51 -85 -93 0 581 1962 1084 1510 855 1568 1078 1079 1840 1891 217 1834 1888 216 184 1832 1877 209 2138 1042 378 40 2132 924 898 1552 1550 1549 1548 369 1934 1400 920 2139 577 917 892 2068 1973 341 1404 224 1394 1399 0\n2141 -166 -13 -170 51 -85 -93 0 2140 581 1962 1084 1510 855 1568 1078 1079 1840 1891 217 1834 1888 216 1855 215 184 1832 1877 209 2138 378 1977 558 1552 1550 1549 1548 369 1934 1400 577 917 892 1973 1404 1394 2090 2054 220 214 1883 0\n2142 -13 -170 51 -85 -93 0 2021 2138 1042 1510 2132 579 1975 1225 924 898 157 363 1933 1552 1550 1549 1548 184 866 855 1563 2140 2141 791 1046 206 1038 1869 1039 1017 1903 1967 341 1036 224 1065 1029 1222 1064 1033 1220 1069 1564 1940 1223 1964 1514 390 522 1257 393 1997 1636 0\n2143 166 167 38 13 727 141 -85 -93 0 2132 159 155 791 1046 1038 1039 1040 1871 141 144 216 2074 0\n2144 167 -170 51 -85 -93 0 581 1977 558 363 1917 374 1508 2142 1823 857 2132 867 2138 1042 378 1962 1084 1510 40 924 898 1552 1550 1549 1548 369 1934 1400 2143 139 577 917 892 1568 1973 1078 1404 1079 1394 1834 1840 1853 1855 1888 1891 209 215 216 217 1728 2090 214 220 1883 0\n2145 -166 -170 51 -85 -93 0 581 1977 558 363 1917 374 1508 2142 1823 2144 864 920 2132 867 1962 1084 1510 40 924 898 1552 1550 1549 1548 369 1934 1400 139 577 917 892 1568 1973 1078 1404 1079 1394 1834 1853 1888 209 216 1399 0\n2146 -170 326 -85 -93 0 2137 553 2132 579 1952 552 159 155 363 1917 374 1508 581 1977 558 2138 2142 1823 358 1498 857 1912 373 2144 146 151 2145 791 377 2074 475 471 216 832 385 380 1888 1821 2100 179 178 827 1883 1877 214 209 795 10 837 0\n2147 -167 807 -241 -102 326 -85 -93 0 1888 994 1909 386 1864 200 1856 369 377 1941 514 390 137 2146 2137 2132 157 363 1917 1275 1998 1508 1934 383 148 578 920 1974 1992 590 1334 2103 1325 1666 1331 595 1514 523 1964 393 1257 1639 1997 0\n2148 807 -241 -102 166 326 -85 -93 0 1871 1039 2132 579 1975 1225 1952 552 924 898 159 72 1552 1550 1549 1548 369 1922 1561 1966 2147 1046 1038 1042 1947 1331 539 1325 1223 1689 1220 558 1222 669 61 568 1688 0\n2149 -49 -102 166 326 -85 -93 0 363 1917 377 472 1198 2146 2132 155 1275 1998 1508 70 1552 1550 1549 1548 369 1934 383 106 18 216 1856 1153 2148 1686 1685 184 61 1879 1666 1196 588 1512 861 1195 1963 1616 1163 163 1152 1592 0\n2150 186 -779 -13 326 -85 -93 0 2132 866 1563 32 2146 2137 363 1917 1560 1971 557 1275 1998 1933 382 1508 1552 1550 1549 1548 369 1922 375 1564 1666 1064 53 56 588 1512 861 1065 1963 1983 1897 1899 565 559 1901 1233 1628 1750 193 1232 1822 1781 1627 594 163 1988 1616 554 0\n2151 -13 -294 326 -85 -93 0 369 1941 514 390 363 1917 472 1198 2132 579 1952 552 159 157 155 72 70 1552 1550 1549 1548 1934 383 106 32 184 1689 1879 1196 1195 2150 61 595 1514 1685 1964 1325 1257 1331 1997 1936 523 386 393 1639 0\n2152 -186 308 -85 -93 0 390 2132 579 1975 1225 924 898 157 1552 1550 1549 1548 369 1934 383 61 595 1514 1222 1964 1220 1257 1223 1997 503 522 386 393 1639 0\n2153 58 151 50 737 49 781 51 59 149 57 0 1066 1213 1064 1210 1563 1217 1761 1984 564 0\n2154 -102 166 326 -85 -93 0 2146 2137 2132 579 1952 898 363 1917 1275 1998 374 1508 72 1552 1550 1549 1548 369 1934 383 137 377 1941 514 510 1214 2149 2151 2152 1564 1666 51 588 1963 565 2153 224 867 1897 1898 1823 1901 1902 558 200 1977 601 717 618 585 554 1664 148 578 920 1974 2103 590 0\n2155 309 122 186 -38 170 325 189 -800 162 149 0 1666 55 206 1895 1413 1868 1196 552 1418 1023 1412 1980 621 585 554 1664 1616 151 1195 1742 1613 859 0\n2156 166 326 -85 -93 0 2021 2146 553 2132 579 1975 1952 159 363 1917 1275 1998 374 1933 1508 72 1552 1550 1549 1548 369 1922 1561 1972 1934 383 2154 1829 206 1869 1870 1017 1018 1967 655 773 1036 564 599 1029 1033 1940 2152 1564 1666 588 1512 1963 565 1163 1761 1563 1064 1065 1066 1897 867 1901 1153 1152 2155 1935 385 1592 148 861 1663 1823 554 558 618 601 0\n2157 -58 111 141 -178 -168 98 162 108 0 588 1963 1163 1512 224 867 1897 1823 1901 861 1153 1592 1152 0\n2158 111 186 326 -85 -93 0 1552 1550 1549 1548 1508 2146 363 1917 1275 1998 1666 56 1560 1971 557 588 1983 559 2156 577 1986 732 558 1750 1822 1504 1768 1699 1999 72 2132 159 579 1952 552 1689 1963 565 1512 53 1975 1225 924 898 157 155 374 70 369 1922 1374 2001 1934 383 1516 106 2157 1685 1222 1824 1325 1220 395 1761 1331 1223 1920 83 564 1936 1947 1946 366 1984 603 386 378 371 589 550 1727 1352 1521 0\n2159 186 326 -85 -93 0 369 1934 2156 577 1973 1018 1882 1986 138 2146 2137 2132 898 363 1917 1560 1971 557 1275 1998 1933 1508 72 1552 1550 1549 1548 383 1564 1666 51 56 588 1963 1983 732 565 559 558 1750 1822 594 1988 554 2158 163 385 1664 1935 496 148 578 920 1023 1214 1974 284 590 200 2103 1841 1856 1899 216 224 2153 0\n2160 326 -85 -93 0 2132 579 1975 1225 924 898 157 1552 1550 1549 1548 369 1934 383 2156 139 2159 61 595 1514 2152 1222 1964 1929 1940 497 1220 566 1257 378 370 385 1223 1997 1946 503 371 386 1634 365 1945 396 1826 596 1521 1969 1175 1179 1995 0\n2161 -186 -85 -93 0 2132 579 1975 1225 924 898 157 1552 1550 1549 1548 369 1934 383 61 595 1514 2152 1222 1964 1929 1940 497 1220 566 1257 378 370 454 385 1223 1997 377 1946 503 371 386 1634 365 1945 396 1826 596 1521 1969 1175 1179 1995 0\n2162 -362 378 -326 57 0 1953 614 711 748 1553 594 1915 1822 394 0\n2163 -736 -85 -93 0 2161 2160 1953 586 363 1917 1275 1998 1508 72 1552 1550 1549 1548 369 1922 1561 1972 1067 1563 1920 1515 1554 1245 1964 1997 2162 581 1666 588 1963 717 565 585 1761 1642 564 583 655 0\n2164 -150 779 -178 77 122 98 162 -355 0 588 1983 55 564 1511 690 1613 631 1195 558 1196 1823 1879 184 0\n2165 -333 -178 -85 -93 0 2161 1564 2163 1064 1065 1897 1901 588 1963 1001 1919 565 1983 1512 1898 1902 200 193 2132 579 363 1917 1275 1998 1508 369 1922 1561 1966 1957 669 633 631 573 702 1558 675 645 577 594 513 571 599 1658 390 578 920 894 1974 1781 590 119 0\n2166 -298 103 -769 87 290 0 1918 472 364 377 1590 0\n2167 170 -85 -93 0 2161 1564 2163 1064 1065 1897 1901 1153 2132 1552 1550 1549 1548 1066 867 363 1917 1560 1971 557 1275 1998 374 1508 369 1934 383 1666 56 588 1512 1963 1983 1163 559 1152 2165 558 1823 1750 2157 184 861 1822 1879 594 1196 1988 554 2166 163 1198 1616 1195 0\n2168 -85 -93 0 1552 1550 1549 1548 363 1508 1917 374 2132 2161 1564 2163 1064 1065 1066 1899 867 2167 581 2138 1977 378 1042 558 1823 184 2142 341 248 894 2068 1039 1046 1038 0\n2169 -769 186 756 102 86 103 0 1157 1590 1919 1512 1124 1580 1120 0\n2170 -736 -757 150 341 340 0 563 1067 1563 1920 1515 1761 1245 565 1513 1997 659 660 1577 590 591 176 1644 0\n2171 -757 769 737 150 341 -93 0 563 1552 1550 1549 1548 369 1922 1561 1972 2170 1064 1065 1066 1897 59 1901 1578 1153 1513 1152 1593 0\n2172 186 756 150 102 86 341 103 -93 0 563 1564 2169 2171 1120 1127 1963 565 1163 1761 1152 1563 1153 1064 1841 1065 1899 0\n2173 -170 -354 103 -13 -93 0 1971 557 1961 32 2168 1552 1550 1549 1548 1768 369 1922 375 42 45 581 1510 855 1962 1567 564 1084 1078 1079 1840 1891 1121 2172 63 595 1514 865 1964 1989 566 1257 560 1997 1699 1631 1999 92 365 1786 1945 176 913 396 1636 1826 390 1521 1940 1697 370 0\n2174 86 102 -793 152 104 88 756 85 0 1631 365 1786 1945 176 913 396 1636 1826 390 1521 1940 1637 370 0\n2175 350 132 120 -779 102 -793 104 88 170 43 140 103 -205 -93 0 2021 1552 1550 1549 1548 2047 1844 1102 1106 1101 1109 1975 597 1832 1877 209 1879 210 369 1934 1400 383 106 570 1036 1029 1033 1035 1940 112 116 390 1639 165 170 1614 162 163 1396 1762 1394 1737 0\n2176 363 120 115 107 785 -186 235 -93 0 2021 595 1964 1554 1906 350 63 61 1296 1552 1550 1549 1548 369 1934 1306 1017 1295 490 493 1672 1670 447 1753 1223 1220 0\n2177 120 -779 115 107 102 -186 -354 103 -13 -93 0 2021 184 1844 1102 865 1106 1101 1109 1975 1225 595 1964 1257 1997 1989 560 1514 2173 1516 2168 369 1922 375 1961 563 1825 191 1881 211 1971 557 32 1552 1550 1549 1548 1934 383 2047 2176 1967 1036 2175 1029 551 1033 750 1940 594 390 1822 1639 1750 170 559 1614 636 585 0\n2178 -112 -783 770 87 184 -779 106 -752 -186 170 42 -93 0 61 2168 1552 1550 1549 1548 369 1934 383 170 875 1112 1615 924 588 1222 1983 225 559 1901 37 1153 1500 1152 1205 1591 163 0\n2179 102 -186 150 756 -354 103 -13 -93 0 2021 595 1964 1554 1906 350 1257 1997 566 865 1514 61 2173 1516 2168 369 1922 375 1961 563 1825 191 1881 1296 184 1879 1196 210 1844 1102 1552 1550 1549 1548 1934 383 1106 1101 1109 1975 1225 2174 79 364 1918 1939 381 1198 389 1195 2177 176 393 1786 1942 521 396 1789 1672 1593 1295 1306 1967 1036 1029 1033 1035 540 1223 1220 2178 1632 163 385 495 1124 1120 1127 1579 1983 869 559 37 1500 1205 908 933 1222 0\n2180 -120 -779 106 -519 -186 756 -354 103 -13 -93 0 595 1964 1257 1997 1989 560 865 1514 2173 1971 557 184 1832 1877 209 1879 210 32 1552 1550 1549 1548 369 1934 383 176 970 1786 1536 1634 170 386 875 1615 1909 588 353 1983 559 1750 37 1822 359 1500 594 839 1913 1205 1988 380 585 10 616 553 0\n2181 -186 150 756 290 103 -13 -93 0 1560 2173 1971 557 184 1879 1196 32 2168 1552 1550 1549 1548 369 1934 383 1922 1534 65 595 1514 1964 1989 1554 1257 560 1906 1997 350 2179 377 1535 1941 454 473 472 391 514 381 1198 390 1195 2180 2047 1638 169 170 386 1614 1909 1936 503 502 585 1537 1543 353 405 409 398 397 396 1993 636 1541 351 352 1439 559 1540 1748 1427 1750 1428 1822 1896 1539 222 1538 799 0\n2182 150 756 290 103 -13 -93 0 1560 2173 1971 557 1961 563 1275 1998 184 1879 1196 33 32 2168 1552 1550 1549 1548 369 1934 383 2181 1564 1666 56 588 1512 1963 1983 565 1163 559 1761 1750 1563 1822 1064 594 1065 1988 1897 554 1901 1153 1152 1591 2166 163 1198 1616 1195 0\n2183 -178 -150 290 103 -13 -93 0 369 1934 184 1879 564 1962 1016 487 357 472 377 1196 1204 1195 1511 80 1560 2173 1971 557 210 33 32 31 30 1552 1550 1549 1548 1768 1922 1561 53 56 588 1512 2164 1774 1983 717 62 395 559 585 1920 483 1699 1830 366 379 1999 871 1695 0\n2184 756 290 103 -13 -93 0 1560 2173 1275 1998 184 1879 33 2168 2182 80 564 1962 1016 472 377 2183 1666 595 1514 865 1964 566 1257 2174 1997 0\n2185 -150 -186 777 85 0 595 1964 1257 1997 1514 65 80 564 1511 1631 1962 365 1204 1919 1195 388 1613 0\n2186 102 178 -186 290 103 -13 -93 0 184 1879 1196 2184 1121 1889 1893 1079 1560 1961 563 2168 2185 1569 1078 1081 1918 1198 1195 1939 389 1567 79 1891 247 206 309 214 2173 1516 369 1922 375 1825 191 1881 211 1832 1877 209 210 1934 1400 791 2177 577 917 176 1973 1615 1404 166 1394 1396 0\n2187 -120 -102 178 -779 -86 58 170 -93 0 377 1941 1552 1550 1549 1548 106 176 393 1615 523 586 946 908 1331 1981 1684 1334 1325 0\n2188 -87 -186 290 103 -13 -93 0 184 1879 1196 2184 1121 1889 1893 1079 1560 1961 563 2168 2185 1569 1078 1081 1918 1198 1195 1939 389 1567 79 595 1964 1554 1906 350 1257 1997 1514 65 61 1891 247 206 1890 1894 199 192 2173 1516 369 1922 375 1825 191 1881 1296 1552 1550 1549 1548 1934 383 365 1512 1945 396 1672 1295 1306 1967 1004 1940 390 2186 377 1941 391 2187 2047 1638 167 169 170 386 1746 1614 1909 1936 503 585 353 405 409 398 397 1993 351 352 1439 1748 1427 0\n2189 178 -186 290 103 -13 -93 0 2188 184 1879 1196 2184 1121 1889 1893 1079 1560 1961 563 2168 2185 1569 1078 1081 1918 1198 1195 1567 595 1964 1257 1997 865 1514 61 1857 1153 2173 1552 1550 1549 1548 369 1934 383 2186 377 2187 1941 2047 514 390 1639 170 1614 1615 163 593 1591 661 1152 1163 0\n2190 -186 290 103 -13 -93 0 2184 1121 1889 1893 1079 1891 185 1857 1153 1560 2173 1961 563 184 1832 1877 209 1879 1196 210 2168 1552 1550 1549 1548 369 1934 383 61 595 1514 865 1964 1257 1997 2185 1569 1078 1081 1918 381 1198 1195 2188 2189 51 588 1123 1963 1983 18 216 1163 559 996 1888 1152 37 1913 179 1591 1500 380 163 385 838 1614 497 10 170 390 353 1639 1909 393 499 0\n2191 290 103 -13 -93 0 184 1879 1196 33 32 2168 1552 1550 1549 1548 369 1934 383 1560 1275 1971 1998 557 2173 2184 1121 1857 1153 2190 1666 56 588 1512 1963 1983 1163 559 1152 1750 1591 2166 1822 163 1198 594 1195 1988 1616 554 0\n2192 -327 -370 57 0 1954 1988 734 594 1553 1822 1915 394 0\n2193 170 87 -779 186 -13 -93 0 1204 1962 564 1564 33 2168 1552 1550 1549 1548 369 1922 1374 2001 1934 383 1516 1617 588 1963 565 1163 2192 554 1616 163 585 1591 616 1152 553 1153 1841 1899 1065 1064 1067 1563 1920 866 1761 1554 563 1950 650 651 550 577 578 1715 0\n2194 -178 372 166 354 142 106 78 150 76 -13 144 0 1283 1998 31 30 53 55 56 588 1657 1963 699 731 62 1515 866 565 578 557 1692 1703 1999 0\n2195 343 279 -341 166 150 737 -13 0 565 651 1001 578 1841 1899 1065 1064 1067 1563 1920 1515 866 1245 1641 1997 0\n2196 -122 -343 180 -341 756 51 166 87 150 -13 -93 0 1990 596 1978 582 369 1922 1374 2001 1561 1966 1516 395 1515 866 1920 1554 1245 1950 1997 550 1645 1780 1727 176 677 88 96 2044 571 0\n2197 87 -779 186 103 -13 -93 0 2021 1204 1962 1084 564 1564 2191 1927 357 2168 1552 1550 1549 1548 1768 2193 42 44 45 1510 855 2173 1567 1589 694 1078 577 1079 1829 1840 1893 206 1891 218 1869 1121 2172 1978 1017 1923 1033 1029 1036 1985 590 2194 1580 1120 1124 1919 2195 2196 1563 1578 1064 1513 862 1065 1594 1897 1152 1901 1153 0\n2198 -779 186 103 -13 -93 0 2168 1204 1962 1084 2197 365 1512 1919 1617 1580 1124 1510 1120 1567 1121 1078 1889 1079 1893 0\n2199 150 187 214 114 -778 -13 -93 0 369 1922 1561 1198 1918 1000 1984 739 1081 1079 1078 1374 2001 1516 1569 1570 563 856 1780 1613 550 395 1950 1920 1554 0\n2200 187 178 214 114 -778 186 -13 -93 0 1198 1918 1000 1984 589 1962 581 33 369 1922 1374 2001 1516 2199 83 1511 1719 1613 550 395 1950 1920 1554 0\n2201 -87 -242 306 186 103 -13 -93 0 184 1879 1196 2198 1195 1198 1918 1889 1893 1000 1962 581 1984 309 214 388 33 31 1534 1512 1666 1998 2200 596 912 1990 744 656 593 585 1831 795 393 970 385 1536 1910 1942 520 413 1535 354 399 395 353 1654 0\n2202 -242 306 186 103 -13 -93 0 388 184 1879 1196 2198 1195 1198 1918 364 2168 1857 1889 1153 1893 2201 1589 1152 1163 1963 1990 588 596 2200 0\n2203 -279 186 103 -13 -93 0 184 1879 1196 2198 1195 1198 1918 364 1564 2168 1919 1945 1124 396 2202 1121 1020 1120 1789 1963 1580 1163 1512 1589 1152 1153 1841 1858 1901 1899 222 1025 1065 1064 1067 1563 1920 520 1515 866 1245 393 1997 799 593 1987 760 564 1761 563 650 651 577 578 1641 0\n2204 342 343 279 737 -13 0 1001 1841 1899 1065 1064 1563 565 564 1761 563 650 2195 577 0\n2205 306 186 103 -13 -93 0 2203 1564 369 1922 1374 2001 1561 1516 2202 1020 1963 565 1001 1841 1858 1899 222 1065 1064 1067 1563 1920 520 1554 393 1950 799 550 593 1987 2204 1984 760 589 739 596 1780 1727 563 83 1761 0\n2206 343 187 279 737 -13 -93 0 369 1922 1374 2001 1561 1516 565 1001 2204 1841 1984 1899 589 739 1065 1064 1067 1563 1920 1554 1950 550 1780 1727 563 83 1761 0\n2207 -342 131 758 178 379 270 769 186 -13 -93 0 596 1564 184 1879 1196 33 2168 369 1922 1374 2001 1561 1516 1962 1984 581 589 739 1719 1780 83 582 563 2171 772 1569 1120 1763 1121 1891 0\n2208 -122 -343 379 270 769 87 278 186 -13 -93 0 369 1922 1561 1972 659 590 1963 1127 588 1564 1552 1550 1549 1548 59 395 1066 1920 1064 1554 1950 550 2207 564 1000 1840 1893 1891 218 1121 1120 2170 650 2196 577 0\n2209 342 122 758 769 278 737 -13 -93 0 1563 1064 1065 1897 1901 1153 1152 564 1000 1840 1891 1121 1120 2171 1578 650 1513 862 577 1594 0\n2210 -744 30 47 123 38 -825 67 371 48 187 -205 0 1079 1080 1893 76 1211 1021 2054 1773 1924 113 2036 1093 0\n2211 379 186 103 -13 -93 0 2205 1938 2203 1157 365 184 1879 1196 2198 1195 1198 1918 1081 364 1564 33 31 2168 1552 1550 1549 1548 369 1922 1561 1972 1934 1400 596 2206 1963 659 588 1127 2208 1563 1064 1065 1897 314 1901 215 1153 1152 2209 1962 1984 655 2207 581 739 583 1404 1018 3 550 1666 1394 1870 1950 749 1998 206 1554 1257 657 594 449 1997 1014 1822 399 1631 1909 394 100 353 1943 354 1654 139 377 1941 514 1023 1022 1883 1894 214 199 2210 1078 1570 1511 1613 1612 1513 862 163 1597 0\n2212 186 103 -13 -93 0 2191 1927 357 184 1832 1877 209 1879 1196 32 30 2168 1552 1550 1549 1548 1768 369 1922 1561 1564 2198 1195 1198 1918 364 2203 365 2205 1938 359 2211 1969 1990 572 1001 2204 2206 1841 1984 760 101 104 1899 589 739 744 1631 1065 591 593 1997 1064 1067 1563 1944 62 866 360 1693 1268 1999 586 1355 1953 674 1960 553 570 594 758 770 1705 1822 1555 580 1501 840 433 10 353 0\n2213 -342 -379 -186 -13 85 0 595 1964 1257 1997 184 1879 1196 2185 1514 65 1962 1984 1204 1016 744 1195 1918 593 364 1081 1631 365 1786 1919 1121 388 1889 1613 1893 856 1079 1570 1078 0\n2214 -87 38 47 116 117 184 342 -186 -205 -93 0 1084 595 1964 1257 1997 1514 61 1832 1877 209 1879 1196 210 2168 369 1934 1400 383 1512 1786 1121 1889 1893 1079 1000 1078 1918 1567 1198 78 1510 1195 1615 166 170 1638 2187 791 577 917 1973 1396 1404 1394 0\n2215 -166 726 43 47 317 103 -205 -93 0 369 1934 1400 139 577 917 1043 1973 1038 1404 1045 1394 1992 2054 1027 215 1884 0\n2216 112 -519 87 116 117 -186 -93 0 595 1964 1257 1997 1514 2168 369 1934 383 1632 1638 1536 970 0\n2217 -279 371 -379 103 -13 -93 0 744 593 369 1922 1561 739 591 589 2168 2212 2213 1969 1556 1925 396 572 595 1964 1554 1906 350 1257 1997 2191 1917 448 1514 65 63 1927 357 434 184 1879 1196 32 31 30 1552 1550 1549 1548 1768 1534 1919 444 443 388 391 1023 390 1883 1895 214 206 2214 1631 78 79 81 364 1510 1918 1939 381 1198 389 1021 1657 1667 1195 1873 1998 1039 1283 1961 999 1881 1296 1295 2215 1829 1535 2216 170 1615 1708 1678 53 1999 550 1692 726 1500 587 1676 0\n2218 371 -379 103 -13 -93 0 1969 1556 1925 396 1990 1163 572 369 2191 1917 434 2212 595 1964 1554 447 397 1257 1997 566 865 1514 63 1927 357 184 1879 1196 30 2168 1552 1550 1549 1548 1768 1934 383 744 593 2217 365 1157 1001 1631 1152 1858 1901 364 1510 222 225 1918 1939 440 1831 1826 1198 1021 385 1521 910 1195 1866 1873 1634 2050 200 207 170 1367 1156 1615 1999 871 53 1692 0\n2219 87 -47 -379 103 -13 -93 0 162 161 2218 1968 571 1969 572 2212 595 1964 1257 1997 1989 560 865 1514 184 1879 1196 32 2168 1552 1550 1549 1548 1768 369 1934 383 1631 1634 81 364 1510 170 1704 1918 1999 1198 1346 1195 1915 1614 394 554 1822 1988 594 0\n2220 -47 -379 103 -13 -93 0 2212 595 1964 1257 1997 1514 369 2191 1917 434 184 1879 1196 2168 1552 1550 1549 1548 1934 383 162 214 309 1121 2219 365 1786 444 443 176 391 390 2047 1635 1638 364 1510 170 1918 1614 1198 1195 0\n2221 -86 176 -87 103 -13 -93 0 365 1919 388 1512 92 2212 595 1989 560 65 184 1879 1196 32 31 1552 1550 1549 1548 79 364 1510 1918 381 1198 1657 1195 1998 1615 1283 176 593 1971 2177 2047 1987 557 1614 756 1537 1543 559 1538 1541 1750 1540 1822 1539 0\n2222 86 116 117 -87 746 -186 85 0 595 1964 1257 1997 1514 1567 1635 1078 176 1079 1786 1840 1121 1891 0\n2223 -87 -379 103 -13 -93 0 2220 2168 2212 2213 1084 1969 1556 1925 396 572 369 2191 1917 434 595 1964 1554 447 397 1257 1997 566 1514 65 184 33 31 1934 383 365 1512 1919 444 443 388 391 390 2222 364 2221 1918 170 586 908 381 1638 1953 1826 1657 176 553 1521 1998 2214 2050 138 1661 0\n2224 -176 -86 47 123 160 124 -793 317 152 104 88 58 103 -205 -93 0 78 1331 1552 1550 1549 1548 106 166 170 586 908 1981 1826 1334 1027 1521 1325 1903 2050 1256 1684 1039 176 946 2215 1576 2069 0\n2225 -178 -379 103 -13 -93 0 184 2212 61 1514 865 595 1964 566 2191 1917 1554 448 1257 1997 369 434 447 397 1969 572 1556 1925 396 2220 2168 2223 1631 2224 1879 1196 364 1918 1198 1195 381 1510 1989 560 65 1832 1877 209 210 32 31 1552 1550 1549 1548 1934 383 55 588 1657 1983 2192 1998 559 554 1283 1614 1971 163 585 557 1634 616 1750 386 875 553 1822 1909 37 839 353 359 1500 10 1913 380 0\n2226 -379 103 -13 -93 0 369 2191 1917 434 2212 595 1964 1554 447 397 1257 1997 448 566 865 1514 61 184 1832 1877 209 1879 1196 210 2168 1552 1550 1549 1548 1934 383 1969 572 1556 1925 396 2220 2223 1631 364 1510 1918 381 1198 1195 2224 2225 1615 176 593 2047 1954 1987 1614 756 163 585 559 1634 616 386 875 553 1909 37 353 359 1500 1913 380 500 10 394 839 1822 0\n2227 -184 176 -779 87 379 104 -186 267 103 42 -93 0 595 1964 1257 1997 1514 2168 1631 364 1918 381 1510 1552 1550 1549 1548 369 1934 383 176 593 2047 1987 661 1614 756 1163 163 559 1591 1634 1152 386 875 1153 37 1901 359 1025 426 429 0\n2228 176 87 103 -13 -93 0 184 1879 1196 2212 595 1964 1257 1997 1514 2168 1631 364 1918 1198 1195 381 1510 2226 1989 560 566 2185 865 65 369 1922 2191 467 210 32 31 1552 1550 1549 1548 1768 1934 383 2227 1615 55 588 1657 1963 1983 2192 1998 565 1163 559 554 1283 1614 1961 1971 163 563 557 1591 1700 1152 1999 1153 1346 1901 429 1025 0\n2229 87 103 -13 -93 0 2226 596 2212 595 1964 1257 1997 566 1514 2168 369 1934 383 1631 364 2228 170 908 1632 1826 385 396 440 1945 0\n2230 103 -13 -93 0 184 1879 1196 2168 369 2191 1917 434 2212 595 1514 2185 1964 566 2226 596 2229 365 1919 1945 444 443 388 396 391 390 1826 913 1786 1121 1889 1891 309 1893 247 214 2199 206 1195 2214 1204 1962 0\n2231 -186 184 187 -87 -13 -93 0 184 1786 1121 1891 247 206 1879 309 214 1889 1893 365 1919 388 2230 378 1929 390 147 1196 2168 2185 2214 2199 1962 1195 1204 0\n2232 187 88 152 -87 -13 -93 0 365 1945 396 1919 388 2230 861 184 1879 1196 2168 1826 913 1786 1121 1889 1893 1079 2231 2200 1195 1204 1617 1962 1510 1084 1567 1078 0\n2233 -779 186 744 178 85 0 1204 1617 1962 1510 1084 1567 1078 0\n2234 -778 744 122 114 -13 0 1198 1613 1918 1511 856 1081 1570 1078 0\n2235 184 56 -87 -13 -93 0 365 1919 388 2230 378 1929 390 861 147 184 1879 1196 2168 1786 1831 1121 393 1889 1891 309 520 1893 247 214 395 1079 206 2234 1195 1204 2233 1962 2214 0\n2236 744 -779 746 135 61 -376 120 -772 168 96 125 178 -13 85 0 184 1844 208 1078 2233 1567 865 1510 1178 152 170 598 1614 1981 585 721 0\n2237 -779 746 135 61 -376 120 -772 168 96 -87 125 116 178 117 -13 85 0 365 1919 1124 184 1844 208 2236 1079 1840 1891 1121 1120 1580 865 2222 1178 152 1510 170 598 1614 1981 585 721 0\n2238 -187 -87 -13 -93 0 365 1919 1124 369 2230 378 1947 539 397 398 1929 390 861 147 184 1879 1196 2168 1552 1550 1549 1548 596 1521 912 1969 572 1179 2050 1995 2235 176 593 950 2047 1987 760 1084 2237 1195 1198 1918 364 1000 2222 1840 1580 1891 1120 1121 0\n2239 186 -87 -13 -93 0 2238 365 1919 1124 388 2230 861 184 1879 1196 2168 1580 1120 1121 1889 1893 1079 2200 2233 1195 0\n2240 -87 -13 -93 0 2238 2239 595 1514 1964 2232 566 0\n2241 -176 187 -86 -793 152 88 -103 -93 0 378 1929 390 369 1922 479 147 2168 1934 383 170 908 1638 1826 393 396 521 0\n2242 176 -186 -13 -93 0 184 1879 1196 2240 1514 2168 595 1964 1257 1997 1631 364 1918 1198 1195 1510 61 2230 378 1947 1331 861 1552 1550 1549 1548 369 1934 383 106 1615 176 593 950 2047 661 1614 1163 163 585 1591 1980 1152 746 1153 1334 1901 1325 225 1684 0\n2243 -186 -13 -93 0 2021 2240 369 2230 378 1947 539 397 1929 390 861 147 184 1879 1196 33 32 31 2168 1552 1550 1549 1548 1934 383 61 65 595 1514 2185 1964 566 1257 1997 1631 364 1510 1918 381 1198 1195 2242 168 170 172 586 908 2241 1632 1638 1953 1981 596 1521 385 174 176 393 2187 553 598 1969 759 1948 495 499 1579 572 674 563 1436 388 1124 1909 1120 2050 570 1036 1657 994 1029 1998 1888 1035 1283 1661 216 933 2115 138 1122 1744 552 874 1427 1749 0\n2244 -86 186 178 777 0 364 1510 1918 1617 1198 1195 0\n2245 -187 -176 -120 -778 31 -794 769 39 0 586 1981 170 393 1910 354 104 596 910 1990 759 565 1163 563 1152 1640 1156 1511 161 1610 0\n2246 -106 151 -770 167 -13 0 1511 856 1594 0\n2247 151 -770 112 71 520 -778 167 -13 -518 0 2021 2246 1610 163 1536 1597 1535 116 118 1035 1562 1029 0\n2248 -176 -120 -778 -794 -13 -93 0 369 1922 2230 378 479 393 521 1133 396 1910 354 970 1947 539 1561 1972 1257 664 1026 1902 200 1950 550 2168 2240 184 1879 1196 861 2243 2244 1589 148 142 1534 170 2245 1582 1130 1131 1901 1153 1152 2247 1513 1789 2200 1121 1840 1891 0\n2249 -215 176 315 184 -783 -794 186 -93 0 1133 1257 1950 550 1552 1550 1549 1548 1841 1901 1899 225 1131 1025 224 1130 1969 1222 1582 572 924 104 1268 0\n2250 -342 379 -778 131 -13 -93 0 596 2168 2240 184 1879 1196 2230 861 2243 2244 1589 1580 369 1922 378 479 1984 2207 1021 1938 1893 388 2200 0\n2251 -120 184 -778 -794 -13 -93 0 1198 1918 369 2230 378 1947 539 1223 1922 1561 1972 1257 664 1225 1220 1950 550 2168 2240 184 1879 1196 861 2243 2244 1589 1580 1564 479 393 1942 521 2248 2249 1153 1152 1163 1990 2250 2209 395 2208 533 0\n2252 -343 -778 131 -13 -93 0 1198 1918 2168 2240 184 1879 1196 2230 861 2243 2244 1589 1580 1564 1963 1990 2250 2209 1000 2208 1840 1938 1891 1020 0\n2253 -778 -794 -13 -93 0 1257 1950 550 2168 2240 184 1879 1196 2230 861 2243 2244 1589 1580 1564 2252 1163 1152 1153 1857 1858 1121 222 1120 1124 1919 1938 2204 1984 2207 744 593 2251 1831 0\n2254 -794 -13 -93 0 2168 2240 184 1879 1196 2230 861 2243 2244 1589 1580 1564 369 1922 378 479 148 33 1552 1550 1549 1548 1374 2001 1516 1257 1950 1964 550 2253 1195 1204 2233 1962 2162 771 1079 564 553 599 1840 1893 1891 1021 1121 619 1120 554 1124 2171 1919 650 2204 577 1990 1717 596 0\n2255 -779 -13 -93 0 2168 2240 184 1879 1196 2230 861 2243 2244 1589 1564 2254 1997 1245 1920 1067 1064 1065 1897 1901 1153 1152 1631 100 1580 148 1204 2233 1962 1079 564 1840 1891 1121 1120 1789 2171 1594 650 577 0\n2256 -13 -93 0 2168 1552 1550 1549 1548 369 1922 1561 1972 184 1879 1196 2230 148 378 861 479 2240 2243 1564 1580 2244 1589 2254 1997 1245 1631 1920 101 395 1067 1064 1065 1897 1901 1153 1152 1163 1990 2255 1195 1198 2252 1918 550 2209 749 1984 655 594 1021 583 1822 1893 394 2200 1943 1513 354 2246 1597 1612 163 0\n2257 -323 -175 -343 214 38 -778 57 0 585 1993 1439 163 1990 1850 199 192 1198 1918 1950 749 1554 661 594 1920 449 593 1822 395 1436 1028 394 1427 1896 1943 222 354 1831 1612 954 38 1747 0\n2258 131 187 -746 371 -93 0 369 1922 1561 739 589 1374 2001 1516 1727 1780 83 563 1569 0\n2259 -770 167 214 -342 -778 -93 0 1198 1918 1081 1079 1078 369 1934 1922 1561 1972 655 1018 1870 206 583 1984 1552 1550 1549 1548 1163 1990 596 2258 550 1950 749 2257 1554 594 1597 1920 449 1822 1513 395 399 394 1613 528 1511 353 1570 1569 139 563 1509 1961 1656 1283 1998 0\n2260 150 -121 184 337 -379 133 131 -757 -746 179 769 737 77 -93 0 1555 1916 2256 1569 2171 1509 1961 1978 648 574 1560 582 723 573 1823 407 586 1499 352 1757 1821 0\n2261 -341 171 258 -121 151 -379 764 131 -794 152 -342 -93 0 1990 656 585 1984 744 593 369 1922 1561 1972 655 583 589 2256 106 1961 1978 1560 723 407 586 1141 1642 1757 1138 71 1140 0\n2262 -215 214 -342 758 769 737 -298 -93 0 1918 1081 1079 1078 1850 199 192 369 1934 1922 1561 1972 655 1018 1870 206 1984 739 591 589 487 357 1932 358 364 2168 1552 1550 1549 1548 1841 1857 1899 1121 1065 1120 1064 1124 1067 1563 1919 1938 1920 1944 62 1515 365 359 366 1554 1245 360 1950 1997 1693 550 610 1999 2258 552 1144 1355 103 596 1960 1789 1969 744 594 758 572 593 1822 1555 1916 433 1229 2260 83 2261 563 1648 586 876 840 1953 1228 1231 1227 0\n2263 -150 71 122 180 52 31 23 -778 300 0 1511 1612 1613 385 904 388 1513 497 1919 390 365 1781 1783 119 0\n2264 214 -342 758 769 737 -778 -93 0 1984 1198 1918 1081 1552 1550 1549 1548 369 1922 1561 1972 1934 1079 1078 2262 193 1851 1153 200 1152 1163 2259 1990 659 148 920 596 590 2258 550 1950 749 1554 594 1920 449 1822 395 399 394 1943 528 354 353 2263 1570 1569 139 563 1509 1654 1961 1998 1283 0\n2265 122 748 -757 756 51 38 179 737 57 0 1124 1919 365 1563 1578 1064 1513 1065 1897 1898 1901 1902 193 1001 1088 1783 84 1087 2044 1574 1573 393 954 585 901 870 111 1942 1747 1993 1436 1427 1439 0\n2266 -341 764 131 -794 152 80 78 295 756 -342 -298 -93 0 369 1922 1561 1984 739 1934 487 357 1932 358 1552 1550 1549 1548 1374 2001 1516 1961 1978 1560 582 470 360 1692 1999 1355 1960 594 1780 1822 103 596 1789 758 2261 1555 1916 0\n2267 -342 758 769 737 -778 -93 0 369 1934 1198 487 357 1932 358 1918 1552 1550 1549 1548 1922 1374 2001 1561 1972 1516 1962 1984 655 581 589 739 1018 591 1870 206 2264 1840 1853 1854 1893 1891 209 210 218 1021 1121 1924 479 1120 1093 1124 1938 359 2265 62 395 1515 1920 1554 1245 1950 1997 550 610 1144 2266 1944 563 2171 360 83 1511 1692 1727 1999 596 1355 1969 760 642 744 1960 572 770 1955 593 594 1648 580 1555 1822 586 876 840 433 1953 37 353 553 1501 10 0\n2268 -379 377 190 -794 152 166 -341 240 150 186 -93 0 594 1961 574 1978 369 1922 1374 2001 1934 1516 1969 1990 759 723 572 565 651 765 1014 578 573 503 1641 1714 397 1521 2050 0\n2269 -122 78 87 -341 342 186 -298 -93 0 1961 1560 1917 650 577 1978 582 574 1918 1000 1834 1888 216 1855 564 369 1934 487 357 1932 358 364 2256 2168 1552 1550 1549 1548 1922 1374 2001 1561 1516 62 395 1515 1920 1944 366 1554 1245 360 1950 666 1997 1692 550 610 599 1999 552 1355 1960 594 1822 394 1943 354 2268 596 1727 1780 96 621 1761 554 1509 1823 558 1499 1957 573 688 1714 1555 1371 578 432 2000 698 352 1711 587 1821 819 831 16 0\n2270 758 769 186 -778 -93 0 1564 369 1934 1198 487 357 1932 358 1918 2256 1552 1550 1549 1548 1922 1561 106 2267 564 1000 1834 1840 1893 1888 1891 218 1121 1120 1124 2171 1919 1938 1961 650 365 359 574 1283 577 1998 2269 1563 1578 1064 52 1513 1065 1066 1625 1897 1899 1901 1233 193 1153 1001 1232 1783 1152 1990 2044 1240 1593 1594 767 393 952 1959 71 1509 148 1334 1910 1942 1686 1019 1823 354 1325 1937 868 1331 353 1652 545 377 0\n2271 -150 131 -794 88 152 80 334 -178 -778 -93 0 1512 53 369 1934 1198 487 357 1932 1074 358 2256 2168 1922 1374 2001 383 1561 1516 106 83 564 1511 1962 1984 690 624 581 589 739 631 1727 591 1076 995 596 1071 1879 1969 642 744 1073 210 572 1355 593 71 1774 1999 1648 1696 170 0\n2272 769 186 -778 -93 0 1564 1198 1932 1074 1918 2256 369 1922 1374 2001 1561 1516 106 2270 1127 1580 1963 1983 56 565 1163 559 1152 1153 1841 1899 1065 1064 1067 1563 1920 62 1515 366 1554 1245 1950 692 1997 550 2271 1761 71 563 1073 651 1071 578 1076 1957 630 633 631 573 702 624 645 577 594 1000 599 1722 1855 2268 596 0\n2273 379 171 169 161 371 -746 179 -93 0 369 1922 1374 2001 1516 596 2258 550 749 726 594 587 1723 0\n2274 150 47 -828 162 353 -746 -342 179 -93 0 369 1922 1561 690 693 580 573 1962 581 1984 2256 1552 1550 1549 1548 1374 2001 1516 106 1570 1569 71 563 1978 582 2273 1990 723 656 651 586 585 578 1378 1830 155 579 944 1417 702 834 594 1822 0\n2275 -743 186 -778 -93 0 369 1922 1561 1198 1918 2168 364 2272 1589 1512 1580 1157 1919 1124 1120 1121 1889 1893 1000 1984 739 1423 1962 581 690 1081 1079 1078 388 94 1374 2001 1516 1076 1566 1957 36 573 693 1666 580 1998 1275 517 1418 1023 1412 1883 214 2274 83 1511 2273 1613 744 395 593 1920 520 1554 393 1950 799 550 912 1727 0\n2276 186 -778 -93 0 1198 1932 1074 1918 1081 364 2256 2168 369 1922 1374 2001 1561 1972 1516 106 2272 1157 1589 1919 93 94 1512 388 1124 1580 1120 1121 1889 1893 1079 1000 1078 655 583 2275 1071 1073 71 1569 83 1511 1613 395 1515 1920 520 1554 1245 393 1950 1997 1611 550 170 1727 1642 596 585 760 1993 0\n2277 -342 -778 -93 0 1198 1932 358 369 1934 487 357 2276 65 1514 1918 364 2168 595 1964 1257 1997 1631 365 1919 388 1613 41 1586 1511 38 92 1945 396 1554 1906 350 1618 1989 560 1074 1081 2256 1552 1550 1549 1548 1768 1922 1374 2001 1561 1972 1516 106 1984 655 657 1217 1018 586 1210 1870 1211 206 1892 1893 1894 192 1079 199 1078 1147 1569 1145 71 563 1151 1073 1978 652 1958 636 1071 582 579 580 585 1076 1957 632 573 578 1721 0\n2278 -333 -778 -93 0 2276 595 1964 566 1514 1198 1918 364 2168 1257 1997 1631 365 1945 396 2277 1000 1840 1891 1121 1786 913 1826 596 1969 572 1521 1919 1020 1983 65 388 1613 43 1554 1920 1989 560 1552 1550 1549 1548 1768 369 1922 1374 2001 1561 1966 1516 1957 669 631 632 573 1558 577 578 1720 538 2050 397 0\n2279 -778 -93 0 2256 2168 369 1922 106 1198 1918 1932 364 1074 2276 65 595 1514 1964 566 1257 1997 1631 365 1919 1945 388 396 1613 1511 2277 1000 1840 1891 1121 1786 176 913 1826 1521 2278 1076 1071 1073 191 897 1881 2174 1256 211 377 905 473 382 891 75 0\n2280 86 104 88 22 756 344 43 171 150 -93 0 1257 1997 566 2168 369 1922 75 2174 382 377 473 0\n2281 -87 22 242 344 -741 171 150 96 -93 0 1121 1257 1997 566 106 2256 1073 191 1881 211 2279 1072 1879 1196 1195 1832 1877 209 210 1552 1550 1549 1548 365 1512 1786 1919 1945 176 593 913 1124 1020 396 2047 1954 1120 1983 1580 559 1514 1826 897 1256 170 386 875 1909 353 2280 364 1510 1918 1614 381 585 37 616 359 1500 553 1913 380 500 10 394 839 1822 0\n2282 -112 -185 142 327 -186 -86 -779 41 42 0 554 364 1918 381 1510 170 386 875 839 1614 1909 37 585 353 359 1500 616 1913 553 380 10 0\n2283 -370 -186 159 151 -187 87 51 344 -741 150 141 -93 0 2021 595 1989 560 61 106 2256 1073 191 1881 1296 1257 1997 2168 101 1631 79 1554 1906 350 103 364 1939 389 1672 1295 1306 1967 1036 1029 1033 1940 390 570 596 1969 572 1510 897 566 2279 1072 1879 1196 1195 1832 1877 209 210 71 1552 1550 1549 1548 1768 369 1934 383 1983 2192 559 554 1702 1999 1346 1915 394 1822 2282 1632 1639 161 163 385 393 910 1614 1935 522 523 84 397 893 2224 0\n2284 -186 -187 87 -214 344 -741 150 141 -93 0 1257 1997 2168 101 1631 364 1918 1510 1893 1211 1554 1906 350 103 1773 1840 1891 1121 1789 218 2279 1072 1879 1196 1195 369 1934 383 595 2283 588 1020 743 495 593 385 1615 1632 170 0\n2285 -187 87 -214 344 -741 150 141 -93 0 1840 1891 1121 1554 1920 1067 1257 1997 2279 1072 1879 1196 1195 106 2256 1073 71 2168 1552 1550 1549 1548 369 1934 383 101 103 1631 1789 1510 1593 2284 1564 2244 1064 588 1065 2192 1897 554 1901 1616 1153 163 1152 1591 0\n2286 -86 768 186 87 777 -93 0 2279 1195 2168 1552 1550 1549 1548 369 1934 383 1510 2244 588 1963 2192 1163 554 1152 1616 1591 163 0\n2287 186 87 756 344 -741 150 -93 0 1554 1920 1067 1257 1997 1072 1879 1196 106 2256 1073 71 2168 1564 1064 1065 1897 1901 1153 2286 1589 1631 1152 100 1593 1789 0\n2288 -770 756 122 149 150 0 1163 1593 1963 1513 1127 1578 1120 0\n2289 -123 159 307 107 -186 -741 -93 0 389 106 2256 1073 191 1881 1072 1844 369 1922 396 1766 484 521 570 1010 393 1967 1975 2176 1225 0\n2290 87 -214 344 -741 150 141 -93 0 106 2256 1073 71 1554 1920 395 1840 1891 1121 2288 1893 218 1257 1997 566 2279 1072 1879 1196 1195 2168 1552 1550 1549 1548 369 1934 383 2285 2287 1514 1631 79 364 1510 1918 1939 389 1021 1968 571 1098 2289 1789 2032 1826 1088 225 908 1087 1901 193 1153 1781 84 1152 2048 1591 1020 163 2192 1614 554 0\n2291 -214 344 -741 171 150 96 141 -93 0 1257 1997 566 106 2256 1073 1840 1891 1121 2290 365 1512 1786 2281 1919 1945 176 913 1124 396 1120 1580 1514 1826 897 905 1256 0\n2292 -87 -186 756 -86 22 344 -741 171 342 96 -93 0 1514 595 1257 1997 566 2279 1072 1879 1196 1195 1832 1877 209 210 106 2256 1073 1084 564 2168 1552 1550 1549 1548 365 1786 2281 1945 176 593 913 1891 396 1954 1987 1826 756 1763 897 559 1913 1256 386 2282 500 1822 394 0\n2293 -111 133 14 -370 158 170 38 30 22 -779 149 150 141 57 0 2192 554 1983 559 163 385 1614 1948 168 172 586 1436 1747 1953 1981 1427 553 598 1749 0\n2294 206 -370 158 87 -186 -86 38 30 22 -793 -741 150 141 -93 0 1983 559 1552 1550 1549 1548 2192 1514 1510 2279 1072 1879 1196 1195 1832 1877 209 210 106 2256 1073 71 2168 369 1934 383 185 996 1913 1015 1976 552 2293 1632 386 2282 500 1822 394 0\n2295 -112 -370 -186 106 -86 -779 41 42 57 0 1983 559 2192 1510 386 875 2282 37 1822 359 394 426 1915 0\n2296 -112 -186 106 -86 -779 41 42 57 0 595 1510 170 2295 588 743 1615 593 0\n2297 350 -370 112 87 -186 -86 38 222 22 -793 -741 150 141 -93 0 1514 369 1934 383 2168 1632 385 1935 391 161 199 106 2256 1073 191 1881 211 1072 1832 1877 209 1879 210 1400 1534 570 1004 1940 390 2216 1535 791 2294 577 917 1846 1973 215 1404 1396 1394 0\n2298 -186 756 344 -741 171 342 96 141 -93 0 2168 1084 564 2291 1079 1078 1567 79 1000 1939 389 1918 381 106 2256 1073 191 261 206 1850 192 1554 1920 395 1906 350 1257 1997 1881 1296 2279 1072 1879 1196 1195 1832 1877 209 210 1552 1550 1549 1548 369 1934 383 1514 2292 2296 1632 385 1948 495 536 388 1124 1120 1127 2297 396 1667 1967 1295 1306 0\n2299 756 344 -741 171 342 96 141 -93 0 2168 1084 564 2291 1079 1078 1567 1072 1879 1196 2298 2287 2244 1512 0\n2300 -370 158 58 47 -756 170 106 38 30 22 -779 42 233 149 150 141 57 0 1121 1891 185 209 1983 2192 559 996 37 1913 1500 380 1015 1976 552 2293 795 585 872 616 1123 553 216 837 10 1888 179 0\n2301 -87 -756 115 106 38 744 222 22 122 67 -741 342 141 -93 0 1072 1879 1121 309 214 2168 1084 1078 1567 1510 79 199 106 2256 1073 191 1881 1296 211 2279 1196 1195 1832 1877 209 210 71 564 1552 1550 1549 1548 369 1934 1400 365 1512 1919 1945 2233 388 396 61 595 1667 1295 1306 1967 570 1004 1940 390 2300 743 593 1615 2214 166 391 1941 377 791 577 917 1973 1396 1404 1394 0\n2302 344 -741 171 342 96 141 -93 0 106 2256 1073 191 1881 1296 211 2279 1072 1879 1196 1195 1832 1877 209 210 1084 564 2168 1552 1550 1549 1548 369 1934 1400 383 1534 1554 1257 1906 1920 1997 350 395 2291 192 1850 1079 1000 261 1078 1918 1939 206 1567 381 389 79 1510 2299 1121 1857 309 1153 214 2301 2286 1514 2296 1632 385 1935 1948 497 495 391 536 390 388 2216 1638 396 1667 1535 176 1295 791 1306 577 917 1967 1973 2297 1404 588 1394 1615 2054 166 0\n2303 -242 186 777 746 -93 0 2279 1195 2168 1857 1889 1153 1893 1079 1078 2233 1567 1512 2286 0\n2304 744 737 186 777 149 342 -93 0 2279 1195 1084 564 2168 1078 2233 1567 588 1512 1963 2286 565 1153 1761 1841 1563 1899 1064 1065 0\n2305 343 87 737 186 777 149 150 -93 0 2168 565 1163 1761 1563 1064 1065 1897 1901 1153 2286 1152 1589 0\n2306 87 737 186 131 777 149 171 150 -93 0 2168 369 1922 1374 2001 1516 2305 1963 1990 588 596 1135 2244 1727 1589 96 1761 1593 1758 1563 1152 1795 1153 0\n2307 -741 171 342 96 141 -93 0 1084 564 2256 106 1072 1073 1879 71 1196 2302 1950 1964 550 595 1069 2303 1121 2306 365 1512 1919 1580 1124 1120 0\n2308 -87 186 -269 171 746 -93 0 1932 381 2168 369 1922 1374 2001 375 1516 94 365 1512 1919 1580 388 1124 1120 1121 1872 2303 1196 1878 1881 191 1825 563 1509 1961 1283 1998 1657 395 1920 1944 1554 421 1950 1009 550 1992 1727 759 596 0\n2309 -234 -269 342 -93 0 1932 381 1912 1559 2168 1552 1550 1549 1548 369 1922 1374 2001 375 1516 1868 1878 206 1881 191 1825 563 1509 1961 650 574 1283 577 682 1998 1829 553 377 1941 508 388 1657 59 395 1920 501 520 1554 386 393 1950 2047 1653 550 157 379 899 1715 484 1132 578 1133 1130 1992 1135 759 0\n2310 306 131 134 166 354 98 242 298 -93 0 1283 1998 574 381 1552 1550 1549 1548 369 1922 1374 2001 1516 388 1020 1657 2192 699 395 554 578 501 520 1715 386 393 157 1653 0\n2311 102 -77 166 354 98 186 -779 -269 -93 0 1498 1283 1998 1932 381 1912 373 1552 1550 1549 1548 1768 369 1922 1374 2001 1516 791 857 1617 55 56 588 1657 1983 699 395 559 578 1944 1720 421 157 378 1276 0\n2312 -149 186 -269 342 141 -93 0 1084 2309 1196 2303 2279 1195 1876 1912 1559 1932 2256 563 1509 1961 1978 650 574 577 682 1823 553 2311 377 1941 471 508 1015 2310 706 550 0\n2313 186 -269 171 342 141 -93 0 2309 1196 1912 1084 564 2168 1552 1550 1549 1548 369 1922 375 1516 1564 2308 2303 1121 2312 1825 2305 2306 191 1963 1990 550 1852 588 1127 1950 749 2244 1120 594 1589 1822 2171 394 652 482 1010 0\n2314 -306 -186 -779 41 42 298 -93 0 595 1964 1257 1997 1514 381 2168 1552 1550 1549 1548 369 1934 383 1919 495 365 385 1631 1632 2296 0\n2315 354 114 122 -742 0 1074 1932 381 1560 1283 1927 1998 357 1657 1565 34 0\n2316 -98 -742 0 34 374 1565 1927 357 0\n2317 -76 -94 350 262 184 -111 41 132 0 2021 1036 1029 1033 405 351 385 458 353 357 1496 1911 367 1557 460 456 1820 668 1060 380 822 553 994 10 1888 836 1058 1063 1057 0\n2318 -827 -77 172 102 15 123 -120 175 47 -86 -205 332 757 143 152 88 -779 132 141 57 0 393 1910 1341 176 1510 557 1404 1973 635 577 559 791 1750 206 1822 1895 594 841 325 1988 1121 554 1343 1120 1789 1614 1337 1579 1736 908 863 935 1826 1340 910 0\n2319 87 -186 -779 41 42 -742 141 -93 0 2021 1516 2168 369 1922 375 65 1074 1932 2314 388 2315 1961 563 1825 191 1881 1296 1839 1971 1124 595 1964 1554 1906 350 1257 1997 1989 560 566 1514 1912 1559 1970 551 381 1552 1550 1549 1548 1934 1400 383 1534 1631 78 79 364 2296 1939 1632 389 161 163 385 1935 1948 497 391 536 390 1638 396 2216 176 393 880 1672 1535 1910 413 1295 1306 1967 1036 1029 1035 112 116 2317 1565 2318 1394 2054 215 907 315 1826 225 0\n2320 -111 112 -87 -205 -186 342 -93 0 595 1964 1257 1997 1514 2168 369 1934 383 161 385 1935 497 391 390 1638 176 1786 2214 1121 206 325 1895 0\n2321 -120 111 -87 -205 58 234 57 0 176 393 1786 1942 1121 1436 1889 1890 1891 309 1893 1894 247 214 192 199 206 795 585 954 1993 1746 1439 1427 0\n2322 112 161 -87 -21 -186 234 289 342 96 -93 0 365 1945 396 191 1881 1839 595 1964 1257 1997 566 1514 61 373 1552 1550 1549 1548 2320 1052 2321 1256 379 897 1908 482 1826 352 394 225 1822 315 594 833 1049 1821 1048 552 1054 751 1981 0\n2323 -112 -87 -21 -186 -779 41 42 106 171 342 -93 0 365 1945 396 191 1881 211 595 1964 566 1514 1084 564 2168 1552 1550 1549 1548 2296 1567 1078 1079 1840 1891 1121 1786 913 1826 897 905 2280 0\n2324 171 342 96 141 743 -93 0 2279 2168 1552 1550 1549 1548 369 1922 1374 2001 375 1516 2307 1071 1074 1912 1932 381 2309 210 1876 1196 209 1195 2313 61 65 595 1514 1964 1257 1997 2314 388 2315 1961 563 1825 191 1839 2319 94 2323 2320 2322 2321 1498 1256 1565 897 357 1727 1911 550 1557 1965 0\n2325 -171 -93 0 2021 2168 369 1922 375 1516 582 1517 1967 1978 1036 563 1029 1825 1035 891 0\n2326 186 -87 777 746 -93 0 365 1919 1124 1512 2303 1580 1121 1120 0\n2327 -87 309 777 123 187 746 -93 0 369 514 390 391 2279 1195 2325 2168 1922 1374 2001 1516 94 1512 1727 550 1950 566 2326 1514 2222 1826 1510 908 913 1615 0\n2328 -186 -102 -213 342 141 743 -93 0 1084 2325 2324 1521 372 1925 396 1839 1879 1196 377 1941 2327 369 514 390 391 1534 1535 2279 1195 210 1833 1877 209 564 2168 1552 1550 1549 1548 595 1514 2319 2216 1964 1071 1257 2290 1997 1000 1631 1918 2296 381 0\n2329 -102 149 342 141 743 -93 0 1516 2168 369 1922 375 1825 191 1839 1879 1196 2325 2324 372 1925 396 1521 1084 564 377 1941 2327 2328 1564 2313 2306 2304 1074 550 1079 1071 1950 2290 0\n2330 186 87 149 342 141 743 -93 0 1516 2168 369 1922 375 1825 191 1839 1879 1196 564 2325 1564 2313 2306 2304 1074 550 1079 1071 1950 2290 0\n2331 87 149 342 141 743 -93 0 2329 2279 1516 2168 369 1922 375 1825 191 1839 1879 1196 1195 210 1833 1877 209 1881 211 2325 2324 372 1925 396 1521 564 1552 1550 1549 1548 1934 1400 383 2330 595 1514 2319 1964 1071 566 1257 2290 1826 1997 1000 261 225 1631 1918 206 315 381 1829 215 2296 577 917 1632 1973 161 1404 1396 1394 0\n2332 149 342 141 743 -93 0 2021 2325 2324 1521 372 1925 396 2032 200 1084 2168 1552 1550 1549 1548 369 1922 1374 2001 1934 383 375 1516 1825 191 1839 1881 1879 1196 2331 86 94 365 2326 2327 1727 61 595 1514 1935 550 818 1964 1989 385 492 1965 566 1240 2321 382 1017 1557 1826 1967 1911 225 913 1036 357 1901 1786 799 1029 262 1121 1123 882 1033 207 1891 309 47 1940 247 214 1235 390 206 2214 1232 147 1626 0\n2333 342 141 743 -93 0 2325 2279 2256 106 2332 71 563 1073 1961 1071 1074 1932 2309 2313 210 1876 1196 65 209 1195 2315 2314 388 0\n2334 -186 -77 354 -742 -269 38 170 -93 0 1932 381 2168 369 1934 383 65 595 1514 2315 1964 1989 388 1257 1919 1938 495 1997 365 359 420 385 377 1632 791 875 858 37 559 873 636 795 585 0\n2335 -735 178 279 -77 -342 -93 0 1498 1516 2168 369 1922 375 2279 1962 1204 1195 1196 1878 1881 191 1825 563 1961 574 1978 1984 589 581 2325 1552 1550 1549 1548 1374 2001 1065 1066 1897 867 1901 1001 1990 596 1727 550 1950 706 726 657 661 580 587 586 593 1379 0\n2336 -736 102 -341 98 -269 371 -93 0 1961 1283 1998 1978 1912 373 369 1922 1561 739 1374 2001 1516 1067 1563 1920 1944 1515 1554 1245 421 1950 1997 378 550 1276 1780 157 596 1969 723 744 572 586 593 1268 0\n2337 -306 -77 -742 -269 -342 -93 0 1962 581 369 1934 1922 1561 1972 655 1018 1870 206 1516 2168 375 2279 1204 1195 1196 1878 1881 191 1825 563 1961 2334 1564 2316 1984 1552 1550 1549 1548 1919 1938 420 377 2336 1064 1066 2335 59 55 2315 0\n2338 333 743 -93 0 2279 2256 2168 1552 1550 1549 1548 369 1922 1374 2001 1561 1972 375 1934 1516 558 2333 1962 1984 655 581 1204 739 1018 1195 1870 1196 206 1878 1879 1881 1072 995 191 1071 1912 1932 1825 2316 1187 381 563 1996 1961 574 1560 1283 1823 1998 1498 2334 1564 2337 388 517 1657 1023 59 395 254 1066 1920 1944 501 520 1064 1554 997 386 393 2336 1950 1959 1653 139 550 587 157 1780 1606 596 593 744 0\n2339 743 -93 0 2279 2338 1957 1977 1559 1204 1912 1195 1074 1196 1071 1879 1072 0\n2340 -121 -379 -342 -341 258 171 -93 131 -794 152 764 0 2261 1990 565 0\n2341 -736 -342 -93 0 369 1922 1561 1984 739 1516 2168 375 2279 2339 1076 1977 1204 1195 1196 1878 1881 191 1825 563 1957 688 1555 1916 2325 1552 1550 1549 1548 1374 2001 1067 1563 1920 1515 1554 1245 1950 662 1997 550 610 594 1780 1144 1822 596 2340 0\n2342 131 215 371 -93 0 369 1922 1561 2339 1076 630 730 588 739 589 1516 2168 375 2279 1977 1204 1195 1196 1878 1881 191 1825 563 1978 1966 669 1558 581 1566 36 2325 2256 1552 1550 1549 1548 1374 2001 1780 596 1521 1969 1990 723 744 572 1001 586 593 1919 1716 1020 2050 1872 397 2007 538 1944 0\n2343 -735 -342 -93 0 369 1922 1561 2339 1076 630 1984 730 588 1957 688 653 580 589 1516 2168 375 2279 1977 1204 1195 1196 1878 1881 191 1825 563 581 573 1566 36 2325 1552 1550 1549 1548 1374 2001 1065 1066 1875 1897 868 1102 1901 2342 550 1950 726 652 657 587 579 1109 586 1379 1101 176 593 1575 701 139 578 1377 0\n2344 -342 -93 0 1516 2168 369 1922 375 2279 2339 1076 1977 1204 1195 1196 1878 1881 191 1825 563 1961 1561 1957 688 573 630 2325 1552 1550 1549 1548 1768 1374 2001 624 653 580 2341 2343 1064 1069 1989 703 722 560 632 636 579 586 578 585 1721 0\n2345 122 103 -93 0 2279 2339 1076 1977 1204 1195 1196 1854 2344 1000 1918 381 1516 2168 369 1922 375 1878 1881 191 1825 563 1961 1283 1998 1561 1957 688 1555 1916 1566 35 1657 388 495 415 385 354 1655 0\n2346 -167 -93 0 2339 1566 2279 1076 1977 1204 1195 1196 1868 206 1516 2168 369 1922 375 1878 1881 191 1825 563 2344 650 577 1829 860 1854 1079 1084 1078 1567 1561 1957 688 1555 1916 1961 1560 407 2325 1552 1550 1549 1548 1374 2001 148 578 1992 759 596 2345 59 395 1920 1554 1950 550 610 1727 993 902 1877 1609 209 0\n2347 -93 0 369 1516 1552 1922 1550 375 1561 1549 1548 2168 2279 2339 1076 1566 1957 1977 36 1499 573 688 1204 1555 1195 1916 1196 1878 1881 191 1825 563 1961 1560 407 352 2344 650 577 2346 1770 579 1952 702 552 594 1821 1822 834 0\n2348 29 0 2347 1994 0\n2349 221 0 2348 198 0\n2350 388 0 2348 1526 0\n2351 197 0 2349 1835 0\n2352 205 0 2349 1842 0\n2353 213 0 2349 1849 0\n2354 -232 0 2349 1859 0\n2355 -236 0 2349 1882 0\n2356 -166 0 2350 1530 0\n2357 -233 0 2351 1877 0\n2358 -234 0 2352 1879 0\n2359 -235 0 2353 1881 0\n2360 -40 0 2354 208 0\n2361 -750 0 2354 1102 0\n2362 -44 0 2355 212 0\n2363 -825 0 2355 1395 0\n2364 -41 0 2357 209 0\n2365 -753 0 2357 1114 0\n2366 -42 0 2358 210 0\n2367 -777 0 2358 1196 0\n2368 -43 0 2359 211 0\n2369 -801 0 2359 1296 0\n2370 -341 381 161 -824 163 171 -122 167 0 2356 395 1920 1554 1950 1376 610 692 550 1964 65 1961 759 574 596 1780 1980 1986 621 585 705 554 599 1718 1717 1714 581 553 25 2162 0\n2371 -179 149 -122 0 96 589 1761 1984 564 0\n2372 149 124 -824 163 171 103 -122 728 0 2349 2355 395 1920 1554 1376 1972 664 597 1950 550 366 1515 2371 1727 103 596 1969 1990 572 565 1767 1761 274 564 1039 655 1038 1018 1043 1928 377 0\n2373 -381 -149 -168 -355 -122 0 2348 2349 2355 563 1961 1560 1927 357 922 866 395 1920 1554 1972 664 1225 597 1966 366 1944 1515 1992 680 691 572 1556 1907 1925 351 396 1622 1767 1220 274 1221 2007 316 1548 1756 1549 1550 0\n2374 -168 -824 163 171 103 -122 167 0 2356 2348 1376 1046 866 922 2372 563 1509 1961 574 2373 2370 573 1498 1957 1823 558 0\n2375 -824 163 171 103 -122 167 0 2361 2349 2359 2356 2348 2021 2363 395 1920 1554 65 1046 1376 1972 664 597 2374 1110 1101 1105 1930 397 1026 2372 1902 563 1509 274 1961 1978 1039 574 1017 1038 1377 1923 1043 573 1498 1033 377 915 1957 1970 1029 1928 558 551 1036 1400 1823 1985 1394 855 590 1734 1737 588 557 731 0\n2376 380 -13 132 68 316 -341 103 186 728 0 2359 2021 2349 2363 397 1978 1017 1923 1033 1029 1036 1985 590 1562 118 117 1961 1560 1927 357 597 1026 1902 274 1039 1038 1042 1043 1929 855 390 1730 1394 1734 1737 588 557 731 0\n2377 -161 168 98 -341 163 171 103 -122 167 0 2359 2021 2361 2348 2356 2367 2366 2364 1110 1101 1105 1930 1978 1017 1923 1033 1029 1036 1985 590 1562 118 1961 1560 1927 357 574 395 1920 1245 1997 1554 1964 1944 360 1515 65 62 1046 573 1498 820 1957 1970 558 551 1823 2376 1991 763 762 745 571 673 771 1558 593 585 581 1204 452 1645 1649 2049 1195 359 1511 170 586 876 1831 1692 37 1953 393 1999 559 1501 553 1910 1355 1958 1199 1960 580 385 594 413 353 994 10 1837 840 1756 1822 1550 1548 1549 0\n2378 -380 170 77 168 -341 163 171 -122 167 0 2359 2021 2356 2367 2366 2364 1978 1017 1923 1033 1029 1036 1985 590 1562 118 1961 1560 1927 357 395 1920 1245 1997 1554 1964 1944 360 1515 62 1991 763 762 745 571 673 771 1558 593 585 1204 452 1645 1649 2049 1195 359 1511 170 586 876 1831 1692 37 1953 393 1999 559 1501 553 1910 1355 1958 1199 1960 580 385 594 413 353 994 10 1837 840 1756 1822 1550 1548 1549 0\n2379 380 -13 68 168 -341 103 -122 167 0 2359 2021 2356 2361 2355 2349 1110 1101 1105 1930 1978 1017 1923 1033 1029 1562 118 1036 1985 395 1920 1245 1997 1515 65 1046 1026 2376 1902 316 551 200 274 1756 1951 750 727 207 1039 1550 572 674 594 1038 1549 586 1044 1548 1268 161 163 1822 593 881 1643 842 2128 87 1340 0\n2380 -380 77 168 -341 163 171 -122 167 0 2359 2021 1978 1017 1923 1033 1029 1036 395 1920 1554 1964 763 2378 771 581 0\n2381 352 -313 175 168 99 -725 -823 -122 167 0 1562 1518 118 1036 395 1920 1245 1997 1515 1556 674 1925 586 396 525 1643 350 95 1713 0\n2382 168 -149 -341 163 171 103 -122 167 0 2359 2021 2361 2356 2355 2349 2363 1509 73 1978 1017 1923 1033 1029 1036 1985 590 1562 118 117 1961 1560 1927 357 574 2375 2001 395 1920 1554 1950 550 1944 360 65 62 1046 1110 1101 1105 1930 397 2377 1190 1996 1187 1912 1926 358 351 2380 597 1026 2379 1902 316 1823 274 1756 558 1039 1550 1977 1038 1549 581 1042 1044 1548 1929 163 385 390 425 1730 359 1394 1692 1999 1355 1960 594 1822 394 2381 1951 1969 551 596 1734 1731 588 554 2192 0\n2383 -121 270 318 13 -168 98 354 103 0 579 1952 552 157 1283 1998 574 394 834 1943 528 354 353 1652 377 420 409 358 352 1823 558 1499 1957 1821 573 0\n2384 -97 13 98 162 0 373 1499 1912 1823 358 0\n2385 -269 309 104 98 -799 -314 0 1932 532 508 381 501 523 388 386 393 1653 0\n2386 -149 -341 163 171 103 -122 167 0 2356 2359 2348 2355 2349 1961 1560 1927 357 1978 1017 1923 1283 1998 574 395 1046 1509 2382 157 579 866 922 1975 1225 2384 1276 377 989 1928 1941 1551 1018 1550 1979 1549 1548 2385 358 1823 558 1957 669 1559 702 1558 1926 594 452 351 1822 1622 2383 1220 1948 1221 385 1902 1044 274 1038 1039 0\n2387 98 13 -168 -341 103 -314 728 0 2359 2348 2355 2349 579 1975 1225 922 157 1961 1560 1927 357 1978 1017 1923 1283 1998 574 2384 1276 377 989 1928 1941 1551 1018 2385 1550 1979 358 1549 1823 1548 558 1957 669 1559 702 1558 1926 594 452 351 1822 1622 2383 1220 1948 1221 385 1902 1044 274 1038 1039 0\n2388 -294 140 -168 -341 0 2359 2021 2363 2348 2355 579 1975 1225 597 1952 552 922 1978 1017 1923 1033 1029 1036 1985 590 1562 118 1961 1560 1927 357 1928 1400 1394 1737 5 551 821 1622 1951 1970 750 1220 674 573 594 1221 316 1756 1014 1550 1909 1549 409 1548 352 1822 1821 834 0\n2389 -168 149 -341 103 -122 167 0 2348 2356 2350 2347 1961 1560 1927 357 1917 363 395 1944 360 62 1046 157 158 159 579 866 1952 552 2387 34 35 853 1689 2388 377 469 791 1765 1043 359 1532 1038 1692 1039 1999 1903 1355 1326 1960 1325 594 1333 7 9 828 1188 1607 1996 0\n2390 -98 -341 163 171 103 -122 167 0 2359 2021 2356 2361 2348 2355 2349 2363 2386 2389 1110 1101 1105 1930 1978 1017 1923 1033 1029 1036 1985 590 1562 118 395 1920 1245 1997 1515 1046 34 853 2380 597 1026 1902 316 200 274 1756 207 1039 1550 1038 1549 1043 1044 1548 377 161 163 1928 1400 1394 1737 551 1951 750 727 572 674 594 586 1822 1268 1642 593 881 842 87 2128 1340 0\n2391 352 -313 175 149 107 172 -350 -802 -122 0 395 1920 1245 1997 1515 1556 674 1925 586 396 525 1642 350 95 1672 0\n2392 -341 163 171 103 -122 167 0 2359 2369 2021 2361 2356 2355 2349 2363 395 1920 1554 1950 550 1944 360 65 62 1046 1961 1978 574 1560 1306 1017 1927 1295 1923 357 1033 1029 1036 1562 1985 117 118 1518 590 2386 2389 1110 1101 1105 1930 397 2390 2377 1190 1996 1187 1912 1926 358 351 2380 597 2379 1026 1823 1902 316 558 274 1756 1977 1039 1550 581 1038 1549 1042 1044 1548 1929 163 385 390 425 1730 359 1394 1692 1999 1355 1960 594 1822 394 2391 1951 1969 551 596 1734 1731 588 554 2192 0\n2393 188 -827 -102 98 77 372 132 172 186 0 590 1737 557 1971 731 574 588 1734 581 855 1977 1823 558 0\n2394 -727 98 68 76 77 124 168 -725 132 172 189 103 -122 0 2363 2348 2360 1036 1985 590 1562 117 395 1920 1245 1997 1515 65 1042 1043 1929 1947 390 398 1730 1394 2393 597 921 745 152 593 946 1649 0\n2395 -231 77 -751 -303 -299 809 103 0 2021 2347 1105 1908 352 1923 1033 1029 1036 1985 1933 363 1874 1903 1022 1326 1772 1325 137 1333 1106 156 0\n2396 168 -303 -299 132 172 -313 381 103 -122 167 0 2021 2356 2361 2363 2348 2360 1923 1033 1029 1036 1985 590 1562 117 1915 1334 598 395 1920 1245 1997 1515 1046 1110 1101 1105 1930 422 397 531 526 358 357 351 2395 1039 1038 1042 1043 2394 1929 1947 853 390 398 1730 1394 1737 597 921 745 152 593 946 1649 0\n2397 -102 77 188 372 132 172 186 0 2363 2348 590 377 1928 1400 1394 2393 1737 853 0\n2398 -231 -168 187 381 285 0 2348 2349 579 1975 597 922 1903 274 346 1027 2032 226 464 1522 1828 372 0\n2399 -168 372 187 132 172 381 285 103 -122 728 0 395 1944 65 579 1975 597 2398 1039 1038 1042 1043 421 2397 358 0\n2400 187 132 172 -313 175 163 171 103 -122 167 0 2369 2021 2356 2361 2355 2392 563 2371 395 1920 1554 665 2375 2001 1374 1922 1950 550 1046 1680 1295 1298 1923 1033 1029 1036 1562 1985 1323 2399 1110 2396 1101 385 1105 795 1930 214 929 397 531 526 310 357 351 1317 1682 1316 0\n2401 -187 172 57 175 381 149 285 103 -122 58 728 0 2021 2347 1334 395 1920 1245 1997 1515 99 596 1969 1990 1556 565 464 1642 1331 1027 586 1325 1903 674 1039 1036 1038 1029 1043 1034 946 933 1327 0\n2402 172 -121 175 163 171 103 -122 58 167 0 2356 2369 2021 394 24 2392 563 2371 395 1920 1554 665 2375 2001 1374 1922 1950 550 1046 2401 1680 2400 1295 551 1298 1951 1923 1033 1029 1036 1562 2391 1518 0\n2403 -172 0 2347 2021 116 118 1034 1562 1029 0\n2404 -350 187 -313 103 352 -122 58 167 0 2349 2356 2359 2369 2403 2362 1915 1553 1960 594 1515 1556 1925 396 395 1920 366 1826 225 315 1756 1550 1549 1548 1822 1046 2032 274 1039 1038 1043 377 1928 383 1044 163 1042 1929 1967 1985 582 1306 1017 1022 2402 1295 1923 1894 74 2391 370 199 1518 107 0\n2405 187 -313 103 352 -122 58 167 0 2356 2349 2359 2021 2347 2403 2369 1915 1553 1960 594 1556 1925 396 395 1920 1554 1950 550 366 1515 1046 2032 1826 274 225 1039 315 1038 1756 1044 1550 163 1549 1548 1822 2404 1036 1029 1033 1034 1923 1517 1298 2402 1295 74 1680 2371 0\n2406 -313 381 103 352 -122 58 167 0 2358 2357 2403 2366 2364 395 1920 1245 1997 1515 1915 1553 1960 594 2405 596 1990 759 758 565 563 1555 1761 1916 564 1511 1962 656 653 581 1016 585 580 1015 412 1642 1913 353 586 876 359 1953 37 553 994 1501 1837 10 1756 840 1550 1822 1549 1548 0\n2407 381 103 -324 -122 58 167 0 2356 2354 1970 1559 1912 358 1951 395 1944 360 62 1046 2406 394 542 1027 1884 1903 1756 1039 1550 1038 1549 1044 1548 385 1822 425 594 359 1960 702 1355 1010 1999 1930 1692 531 357 0\n2408 103 -324 -122 58 167 0 2403 1951 572 395 1920 1245 1997 1554 1515 2407 1981 1992 665 586 713 582 2392 74 575 2389 691 1268 565 593 1643 721 585 0\n2409 -381 308 77 352 -122 0 2359 2369 2021 2355 2349 2356 2348 2403 395 1556 1925 530 1133 396 1179 1995 1920 1554 1950 550 1964 1944 360 62 1981 766 713 1560 1306 1017 1927 1295 1923 424 357 370 1033 359 1692 1029 1999 1036 1562 1355 1985 1518 1960 1022 594 1894 310 273 214 206 1829 989 1551 1550 1549 1548 1822 394 1943 525 354 350 1671 1672 163 1520 2391 1574 1771 0\n2410 -149 175 381 317 77 161 352 97 -122 167 0 2359 2021 1027 1884 1756 1550 1549 1548 395 1556 1925 530 1944 360 62 73 74 563 1961 1978 1560 582 1017 1927 2370 1923 424 357 2001 1033 359 1692 1029 1999 1355 1960 594 1822 394 527 2381 352 579 834 1952 1821 552 0\n2411 363 149 175 57 180 181 -324 -122 0 2359 2369 2021 2403 1951 395 1920 1245 1997 1515 1306 1017 1295 1923 1033 1029 1036 1562 1985 674 1518 727 586 2391 1647 394 593 1822 742 594 0\n2412 175 381 317 180 181 117 39 97 -324 -122 167 0 2021 2369 2403 2347 2367 2348 2356 1027 1884 1756 1550 1549 1548 1970 1559 1912 358 1951 1179 1995 573 572 395 1920 1554 1950 550 1245 1997 1515 2410 2371 2411 1967 1036 1029 1033 1034 1923 1517 1298 1295 1680 596 1521 1990 565 1761 1642 564 170 933 1962 1600 1204 176 393 1195 2016 445 1828 1157 935 2245 0\n2413 -379 149 382 -122 0 1990 760 565 564 1761 0\n2414 -150 -59 187 179 108 111 729 -132 131 0 2369 2403 2362 551 1951 82 83 1511 909 1680 1052 1295 1048 1298 1299 1054 1923 825 674 370 570 107 0\n2415 149 108 -367 111 729 180 181 -132 -122 0 2367 2403 2362 2368 1993 551 1951 1556 1925 396 395 1920 1554 1950 550 1245 1997 366 1515 65 2371 2413 596 1826 2414 1761 1644 565 1789 593 1963 1121 721 588 1889 1890 674 2244 1893 1894 570 192 199 1004 107 1923 1517 382 75 0\n2416 -132 -122 58 167 0 2348 2350 2359 2021 2356 2367 2368 395 1920 1554 1950 550 366 1515 551 821 1951 1970 1556 1559 1925 1912 396 530 358 2408 142 147 149 378 918 1929 1947 2409 1027 1884 1049 2412 163 585 1532 1980 1993 1765 377 1928 383 2415 72 563 896 1978 759 735 582 1017 596 1025 589 1923 424 1826 1901 1033 2414 193 1029 1570 1036 1562 1763 674 1518 1891 1014 721 1121 441 593 1789 1786 364 84 75 901 0\n2417 -149 132 -122 167 0 2359 2021 2349 2356 2403 395 1944 65 74 563 1978 582 1017 2392 1923 378 1033 1929 421 1029 358 1036 1985 1022 1894 273 206 1829 2397 597 1975 2380 579 0\n2418 -295 -350 132 -122 167 0 2349 2356 2348 2403 2360 1985 590 1967 582 395 1920 1245 1997 1554 1944 1515 65 1929 1947 421 1022 398 358 1894 273 206 1829 2397 597 921 1975 745 579 692 593 575 1649 2380 946 665 152 598 0\n2419 -102 187 381 77 286 132 -122 167 0 2021 2348 2403 2356 2361 1046 1033 1029 1036 2418 1042 1038 1039 1903 1027 378 1985 65 377 2397 1941 454 921 523 2399 1754 393 0\n2420 381 269 77 286 -122 58 167 0 2353 2349 2021 2351 2356 2350 2354 2403 2348 2360 1046 2416 1033 1029 1036 2418 1042 1038 1039 1903 338 223 346 226 344 227 274 378 1967 582 395 1920 1554 598 1027 1936 430 1051 1553 1960 594 1822 394 2406 1969 596 1025 2032 1925 1522 372 2419 791 1765 206 1532 293 2402 1049 575 1048 1972 1055 664 945 597 1026 1828 1930 922 379 152 0\n2421 -381 103 180 171 149 -122 167 0 2403 395 1920 1245 1997 1554 1515 1981 665 586 2389 2392 1649 575 593 767 1987 2413 0\n2422 -362 252 251 756 -350 149 -122 167 0 2361 2356 2348 226 395 1920 1554 1964 1962 771 564 763 2413 1761 597 1026 1025 1789 1930 1925 1522 1105 372 1101 1828 1110 922 0\n2423 286 -122 58 167 0 2356 2021 2353 2349 2358 2416 2417 1046 1033 1029 1036 1967 1985 582 590 2418 378 1042 1038 1039 1872 1903 1121 344 346 2421 2422 1016 1932 358 2420 0\n2424 -122 58 167 0 2359 2369 2021 2347 2356 2367 2348 64 395 1920 1554 1245 1950 1964 1997 550 2416 2417 2371 2423 1923 1298 1017 1295 1967 1978 1036 665 1029 1034 1517 1680 596 1521 1969 2413 572 1556 1179 1987 771 1925 1995 593 1204 1678 2016 1195 170 933 1828 597 921 1975 1178 692 393 935 1561 445 544 1157 1027 2245 1903 207 0\n2425 367 151 68 124 176 170 -724 152 116 132 0 2347 2369 2403 2363 1033 1923 1298 1295 1034 1517 114 585 1307 580 822 708 554 1733 1673 1394 1507 1730 1820 1496 0\n2426 343 68 124 368 362 -724 -793 152 88 -295 132 0 2358 1016 1918 364 586 581 1929 390 565 2425 656 721 717 1000 593 1840 1891 1121 1020 1786 1919 1631 437 363 0\n2427 362 -724 -186 -378 -295 39 240 132 736 0 2359 2358 1033 1923 1017 1964 1257 1997 1554 1920 1989 1240 566 1514 1756 1550 1549 1548 1016 722 547 1014 540 1909 502 397 405 396 351 2426 1990 661 596 1135 772 593 2032 1795 1028 200 193 1896 1904 222 214 1831 393 880 1910 1235 1341 1232 1236 1914 519 394 1822 594 841 1988 1340 1343 1337 0\n2428 -343 327 123 -724 143 -727 736 0 2347 2369 2348 554 1033 1923 1298 1295 1034 1517 1042 1929 390 1990 604 596 1135 550 2032 1795 1679 1680 200 193 163 928 91 94 96 1519 1044 1783 119 918 0\n2429 379 -377 123 -724 143 -727 736 0 2347 2369 2348 1988 2428 565 554 1033 1923 1298 1295 1034 1517 1042 1929 390 596 1135 749 2032 1795 550 200 193 1679 1680 163 928 91 94 1519 1044 1783 119 918 0\n2430 131 87 23 31 187 151 135 -724 143 -727 0 2347 2369 2348 1033 1923 1298 1295 1034 1517 1042 1929 390 1679 1680 163 928 91 1519 1044 1783 119 918 0\n2431 87 -769 31 -59 187 151 327 68 176 -724 143 144 -727 132 167 0 2347 2369 2356 225 1901 193 554 1033 1923 1298 1295 1034 1517 114 2430 550 1507 1965 567 1820 822 1675 163 585 1591 616 363 1508 898 553 1917 1659 1275 1998 0\n2432 187 770 151 327 68 123 176 342 -724 143 152 88 144 -727 132 167 0 2347 2368 2367 564 1033 1923 382 1034 1517 2032 1826 200 225 1901 1153 1152 2431 1512 913 1786 1121 1889 1893 192 1000 75 1918 1510 1198 1615 1195 0\n2433 -120 -87 31 -185 -186 57 39 58 0 2358 2352 86 594 1988 1343 393 880 841 2321 1910 161 1341 1340 1337 0\n2434 -184 -187 151 68 -730 368 124 150 -724 152 116 132 0 2347 2368 586 1033 1923 382 1034 1517 176 593 1053 721 905 2425 75 1510 0\n2435 120 184 -187 151 121 68 123 -730 176 124 150 -724 152 125 116 132 122 0 2347 2368 1033 1923 382 1034 1517 799 1053 222 169 905 1896 1437 75 1428 1510 1427 2425 1439 1993 0\n2436 31 -810 23 7 15 -187 -185 -730 30 -186 231 0 207 1340 161 214 1052 292 875 905 839 206 1339 0\n2437 368 124 -362 -724 143 152 -186 231 240 132 122 167 0 2356 2347 1962 564 1034 109 1033 1923 1514 1046 1039 1038 1042 1947 398 1929 390 1756 1550 1549 1548 1768 1049 1563 586 1054 1014 711 1048 1909 502 1553 405 396 1915 351 394 1822 594 1988 1343 2428 565 1163 2429 1969 572 2432 2434 2435 393 880 841 910 1910 1341 1337 2436 200 935 1767 0\n2438 -31 -187 -120 124 -737 0 596 1969 572 103 1069 1964 566 1564 1514 200 935 1767 0\n2439 -185 -730 -810 31 -187 -120 30 -186 231 0 910 880 841 2436 0\n2440 176 -810 31 -187 -120 141 30 -186 -378 57 729 231 149 0 596 1969 572 176 1989 560 1964 566 1768 1056 1048 2439 1822 394 1915 1346 1999 1709 1755 1367 591 1983 579 738 703 0\n2441 -176 31 151 160 23 96 59 184 -807 124 -94 57 -727 58 0 2356 2348 2352 2353 2349 1042 1929 390 933 1828 1327 597 946 1991 791 1043 571 206 918 1895 325 328 330 1121 218 219 1786 1781 119 0\n2442 -187 -120 -807 124 141 -94 -737 57 -727 729 231 149 58 0 393 1910 1341 176 109 1069 1964 566 1564 1768 99 596 1521 910 1969 1990 572 565 2438 2441 2440 1337 1343 1954 1988 594 1822 394 1915 1346 1999 1709 1367 591 579 741 0\n2443 -334 185 187 -724 335 0 2347 2369 1033 1923 1298 1295 1034 1517 560 1958 636 580 585 1677 0\n2444 185 187 316 141 -724 335 57 132 0 560 1822 394 1915 526 1346 351 1999 2443 559 1755 1750 826 557 1497 1820 1956 567 0\n2445 -160 -377 -724 143 -727 736 0 572 1522 1969 2429 0\n2446 379 87 -377 187 350 -793 143 88 -727 736 0 2021 2369 2347 1988 554 1036 1029 1033 1923 1298 1295 1034 1517 570 1042 1947 749 2429 550 396 1766 1679 1925 502 535 126 163 372 386 363 1633 0\n2447 31 -185 187 -120 350 -253 132 58 167 0 2347 2021 2356 2368 393 1910 1341 594 1988 1343 1337 841 2424 1563 1884 1756 1550 1549 1548 1066 1064 1564 880 1903 207 1046 1039 1038 1042 1069 1036 1029 2427 1962 564 1033 1923 382 1034 1517 1964 1257 1997 1989 560 566 1514 1768 2433 2446 1969 1990 1556 565 1163 1907 1925 351 396 1826 2432 225 908 1901 75 193 192 1340 266 214 0\n2448 -120 316 124 350 -253 149 132 58 167 0 2347 2021 2356 1046 1903 1039 1038 1042 1947 1331 2424 1884 1563 1756 1550 1549 1548 1066 1064 1564 1069 1964 566 1989 560 1036 1029 207 2427 2437 1981 1334 1325 1977 558 1034 570 1049 2442 2444 2447 121 200 1766 2032 0\n2449 187 68 -772 123 142 327 121 120 134 124 342 -724 158 67 143 152 88 144 -727 132 122 167 0 2347 2356 2368 2348 1563 2428 1163 565 564 1033 1923 382 1034 1517 1042 1947 398 1826 2432 225 171 172 908 1901 1437 1441 75 193 1427 192 1428 1840 1893 1896 1891 218 1211 222 1121 1773 1831 2036 913 1093 1781 1924 2046 389 84 0\n2450 -176 96 59 352 123 160 120 124 -94 240 122 58 0 1563 1756 1550 1549 1548 1066 1064 1069 1964 1554 1906 350 170 933 1803 1828 0\n2451 112 176 96 -772 120 -727 729 0 2347 1053 1600 1048 147 1055 1044 163 0\n2452 123 -185 120 124 350 -253 132 58 167 0 2347 2356 2021 2368 2366 2364 2367 2424 1884 1903 1563 1756 1550 1549 1548 1066 1064 1564 1069 1964 566 1989 560 1036 1029 207 1046 1039 1038 1042 2427 2437 594 1960 637 559 2445 1988 26 1953 553 1962 564 1033 1923 382 1034 1517 570 1554 1906 350 1514 1768 1049 2429 1969 1556 1179 1907 1995 351 2449 99 1521 2450 2451 905 75 364 2282 1918 1195 1198 0\n2453 -185 120 124 350 -253 132 58 167 0 2356 2424 1563 1884 1756 1550 1549 1548 1066 1064 1069 1964 1257 1997 1989 560 1564 1514 1046 1903 1039 1038 594 2452 103 396 1925 1945 1556 365 1969 2446 0\n2454 316 124 350 -253 149 132 58 167 0 2347 2369 2021 2356 2424 1563 1884 1903 207 1046 1039 1038 1042 1756 1550 1549 1548 1066 1064 1069 1564 1036 1029 2427 1977 558 1033 1923 1298 1295 1034 1517 1989 560 1768 2448 2453 1822 2444 394 99 103 596 1521 1915 1969 1346 572 1999 1755 2450 1958 636 580 585 1675 0\n2455 124 350 -253 149 132 58 167 0 2021 2356 2354 2424 1563 1884 1903 207 1046 1039 1038 1042 1756 1550 1549 1548 1066 1064 1069 1564 1036 1029 2427 1977 558 1964 1554 1920 1989 560 1929 2454 1930 522 538 1010 393 1558 1975 2453 670 754 1822 559 557 1750 0\n2456 -124 167 0 2348 2356 2361 397 922 1930 1110 1105 1101 0\n2457 120 117 108 85 -793 -186 116 57 0 2366 2364 2367 1514 1638 1635 364 1918 381 1198 2296 1195 0\n2458 86 117 85 -793 -186 116 0 2367 2356 2185 1570 1514 1631 2222 0\n2459 -253 149 132 58 167 0 2359 2369 2349 2021 2356 2424 1563 2456 1046 1884 1903 1756 1039 1550 1038 1549 1042 1548 1929 1066 390 1064 1069 1564 1964 1554 1257 1906 1997 350 2455 1967 1985 1306 1017 1022 1295 1923 1933 1894 1033 363 273 1029 206 1562 1829 117 1518 377 1941 391 2457 393 1942 2458 364 1939 536 389 396 1672 0\n2460 -381 -86 335 -186 57 0 2358 2367 2364 2366 364 1918 381 1198 1195 2296 1016 1977 1510 1981 644 586 1054 1553 1915 394 1822 594 1988 554 1614 162 163 585 1052 636 1048 559 1049 1050 1846 877 185 37 0\n2461 -120 104 756 103 304 112 -737 0 2359 2021 2347 1069 1964 1554 493 1017 1967 1036 1029 1034 114 1257 1997 1564 1514 176 393 1786 499 1634 385 0\n2462 -86 -737 253 167 0 2356 2353 2351 2367 2366 2364 2359 2349 2348 1069 1964 1554 566 1564 1514 1989 338 223 344 225 2456 1046 364 1918 1939 381 1198 1195 2296 2460 1027 1936 1947 493 378 1042 1017 1038 1967 1039 570 1872 1873 274 1121 1021 1968 571 1766 1826 596 1521 1969 572 1179 1767 1995 921 2461 1178 0\n2463 -104 140 783 132 0 2348 379 921 1930 1623 1223 1220 0\n2464 -317 112 116 -737 783 132 728 0 2359 2021 2347 1069 1964 1257 1997 1554 1920 1564 1514 1936 1947 543 493 378 1042 1560 1017 1038 1971 1967 1039 557 1036 1872 1029 1121 1034 114 2463 1639 2461 0\n2465 -188 39 168 -120 -185 176 112 253 58 167 0 2353 2351 2352 2356 2365 594 1988 1343 393 1910 1341 1337 841 2424 1563 341 1065 1064 1564 880 176 554 2462 1069 1964 1257 1997 566 1514 338 223 344 225 135 935 1184 2433 1995 1631 1173 363 1508 1925 1917 396 1275 1826 1998 910 1659 1340 14 15 161 162 1117 1119 1113 0\n2466 188 -785 336 152 88 60 59 132 124 0 1623 557 628 572 1556 1828 1925 1521 396 1826 0\n2467 -120 336 112 308 253 132 58 167 0 2353 2352 2349 2356 2351 2348 2360 338 223 1553 1915 394 1822 1046 346 1221 2424 1563 341 1065 1064 390 2464 1027 1981 586 398 1069 1964 566 1564 1514 226 344 225 227 2456 393 522 1223 1026 1220 1975 579 2466 921 2465 152 949 0\n2468 -362 112 308 253 132 58 167 0 2352 2349 2354 2356 1046 346 1221 2424 1563 341 1065 1064 390 2464 1027 1981 1054 2462 1069 1964 1257 1997 1564 1514 1962 1977 1084 644 2467 1053 1048 1049 1855 293 1079 206 1078 1829 1567 377 363 1928 1917 383 1560 1639 1971 2463 557 0\n2469 -240 278 -186 0 2354 2356 2367 1081 1855 293 1079 206 1078 1829 1570 377 2185 436 363 0\n2470 112 308 253 132 58 167 0 2356 2349 2352 2358 390 2424 1563 341 1065 1064 2462 1069 1964 1257 1997 1564 346 1221 1046 2464 1027 1981 1054 2468 1016 1918 2469 1049 1048 1052 1053 385 393 2467 1935 522 391 1026 2458 1975 363 687 1917 1560 0\n2471 -277 -112 116 86 152 88 251 132 124 0 2359 2021 2347 2368 386 1936 170 225 1933 535 382 1017 396 1025 1967 1826 1969 1990 1036 905 1556 565 1029 1907 1034 351 1517 75 564 1962 656 581 2425 0\n2472 308 253 132 58 167 0 2353 2352 2424 1563 341 1065 1064 2462 1069 1964 1257 1997 566 1564 1514 344 2456 390 2470 2471 363 1631 2458 365 391 444 0\n2473 253 132 58 167 0 2352 2021 2359 2369 2424 1563 341 1065 1064 1069 1564 1964 1514 1554 1257 1906 1997 350 2462 2472 1940 1033 1029 1036 1562 1967 1518 1306 1017 1295 1933 363 1631 92 365 1672 1945 396 0\n2474 132 58 167 0 2359 2369 2021 2349 2356 2424 1563 1046 2473 1884 1903 2459 1756 1039 72 563 1550 1038 1978 1549 1042 1306 1017 1548 1929 1295 1923 1066 390 1033 1064 1029 1069 1564 1036 1562 1964 1985 117 1518 1554 1257 1022 1906 1997 1894 350 273 206 1829 377 1941 391 2458 2457 364 393 1939 389 521 1672 396 0\n2475 -120 -86 -737 57 -727 729 231 -186 123 58 124 0 2367 2364 2366 2369 2021 2347 79 595 1964 1554 1906 350 364 1939 389 1672 1295 1306 1967 1036 1029 1034 1978 563 1918 381 1198 1195 2296 1989 2460 755 558 1042 1947 1331 1334 1325 1510 566 1514 176 2442 1826 908 1056 1615 1048 588 1052 2192 163 554 1614 0\n2476 -117 -727 0 147 391 1043 1941 377 0\n2477 -108 0 2347 2021 114 117 1034 1562 1029 0\n2478 -57 0 2357 223 1548 313 1549 1756 1550 0\n2479 -144 0 2478 1768 0\n2480 117 116 85 58 167 0 2356 2477 2478 2424 1563 1066 1064 1069 1964 1257 1997 1564 2474 551 1951 1556 1925 396 2456 1046 2458 2457 2462 1884 1903 1049 1039 2475 1038 0\n2481 -117 58 167 0 2356 2478 2349 2348 2424 1563 1066 1064 1069 1964 566 1564 1514 2474 551 1951 1556 1925 396 1970 1189 1996 572 821 2456 1046 147 391 2476 1941 1038 377 1039 1188 274 921 1767 0\n2482 -116 58 167 0 2356 2478 2347 2349 2424 1563 1066 1064 1069 1964 566 1564 1514 2474 551 1951 1556 1925 396 1179 1995 572 2456 1046 125 390 1929 1940 1042 370 1038 1174 1039 132 274 1767 0\n2483 58 167 0 2348 2356 2478 2349 2456 1046 2424 1563 2474 551 821 1951 1970 572 1556 573 1925 396 1066 1064 1069 1564 1964 1514 566 2481 2482 2480 363 1508 1917 1275 1998 1284 579 1952 1975 702 552 597 594 1767 1822 274 394 834 1039 1943 1821 1038 352 1042 410 0\n2484 353 97 -85 167 0 2352 2356 2478 363 1917 1275 1998 1508 1046 2483 224 1899 248 1039 1038 1042 1947 573 1284 579 1952 702 552 594 1822 394 834 527 1821 352 0\n2485 102 132 188 140 -727 0 2356 2348 2349 1042 1929 1320 791 1043 206 918 1895 1683 330 1316 1317 0\n2486 324 188 -277 167 0 2352 2356 2359 2021 2363 2348 2403 1933 1017 1967 1036 1029 1917 1560 1971 557 1046 2483 224 1899 248 1039 1038 1042 1947 535 396 59 1563 551 2485 377 1928 1400 1394 1737 590 918 639 620 1044 554 560 2428 163 565 1736 0\n2487 188 -85 167 0 2352 2348 2356 2355 363 1917 1560 1971 557 1275 1998 1508 1046 2483 224 1899 248 1039 1038 61 2486 1970 573 2484 1284 821 579 2485 1975 702 377 594 1928 1658 1018 599 773 0\n2488 -85 167 0 2352 2359 2348 2478 2356 2363 2477 1046 2483 224 1899 248 1039 1038 1042 1929 390 2456 363 1508 1917 1933 1560 1275 1017 1971 1998 1967 2487 597 1975 643 579 1553 1284 1915 573 820 394 1970 1822 594 1988 554 1659 553 668 615 1557 1404 1911 1394 357 1730 0\n2489 -120 47 -185 -250 0 2352 594 1988 1343 1899 248 207 1898 1902 200 1897 1901 193 186 393 841 1910 1340 1341 1337 0\n2490 -78 167 0 2365 2367 2477 2488 2483 224 1897 1901 1153 61 59 41 42 359 1500 878 1913 1938 1116 388 1113 1613 1119 1195 163 1617 588 1512 1963 1591 1163 1152 0\n2491 -178 111 167 0 2477 2488 2483 224 1897 1901 1153 588 1512 1963 1591 1163 1152 0\n2492 178 -779 757 167 0 2488 2483 61 1580 2233 1120 1079 1121 1840 1891 0\n2493 -779 757 167 0 2478 2488 2483 224 1897 1901 1153 61 2492 588 1512 2491 1963 2192 163 1163 554 1616 1152 1510 1589 0\n2494 306 167 0 2367 2356 2488 2483 224 1897 1901 1153 61 59 388 1124 2493 1195 1198 1613 1918 1511 364 1081 1570 1078 1079 1840 1891 1121 1020 1120 1963 1580 1163 1512 1152 1589 0\n2495 -242 -778 167 0 2367 2356 2366 2403 1198 1918 2488 2483 61 224 1897 1901 2494 1919 1001 1963 588 2244 1567 1153 1157 1152 2490 59 1889 1891 1893 185 1079 1000 1078 1962 1570 581 1511 1613 37 1513 1501 879 1597 1199 163 0\n2496 -778 76 167 0 2356 2403 2478 2483 224 1897 1901 2494 1919 1001 1963 1127 1153 1157 1152 2490 59 58 1198 1932 358 2495 1121 1120 1578 52 1513 1692 1594 1597 1999 1511 163 1355 1612 1960 354 594 1943 1822 394 0\n2497 -779 167 0 2356 2483 224 1897 1901 1153 2494 1919 1157 1152 59 1204 2493 1962 1578 564 1513 1594 0\n2498 167 0 2356 2352 2367 1046 2483 224 1899 248 1039 1038 1042 1929 2494 507 2497 357 1195 2496 0\n2499 -39 0 2498 143 0\n2500 -53 0 2498 146 0\n2501 -103 0 2498 148 0\n2502 -117 0 2498 150 0\n2503 -181 0 2498 151 0\n2504 359 0 2498 578 0\n2505 -116 0 2498 2348 919 0\n2506 -372 0 2504 1974 0\n2507 -381 0 2504 1992 0\n2508 -180 0 2506 590 0\n2509 -806 0 2506 1323 0\n2510 -189 0 2507 598 0\n2511 -809 0 2507 1334 0\n2512 150 736 -114 -770 -298 0 2356 2507 2498 2478 2501 2510 2360 388 1919 365 1938 862 1513 1163 1932 358 1918 1081 1570 1593 1078 563 1509 1079 1961 1840 1893 574 1891 218 1823 2384 1121 558 1957 755 1189 1069 1996 1064 1065 1066 1897 1899 868 1901 251 1188 193 214 377 1783 2044 1941 393 952 2489 523 1942 1822 398 2383 152 0\n2513 -313 756 122 -114 -770 -778 0 2403 2367 2479 2359 2501 2478 2347 1163 1963 1127 1120 1198 1563 2512 564 1984 589 1511 388 1919 365 1513 1915 1943 361 354 1612 163 385 904 1595 1948 413 72 563 1509 399 353 2185 1961 1978 1564 1824 1283 1017 224 1998 1923 1897 1654 370 1901 137 193 2265 1781 1094 0\n2514 -185 122 -114 -770 -778 0 2403 1198 1563 2512 1511 388 1938 359 1513 52 1932 358 594 1504 1960 1553 1355 1905 1999 415 1692 354 357 1612 1927 163 1560 1595 1961 563 0\n2515 122 -114 -770 -778 0 2478 388 1919 365 1513 1198 1563 2512 564 1511 1984 589 2514 1822 394 1943 2513 354 1121 1612 1857 1865 163 904 193 1088 1783 84 1574 389 1087 1924 1093 0\n2516 -242 51 52 -114 0 2505 2508 388 1919 365 1513 1857 1865 193 200 1783 1781 119 0\n2517 23 179 51 52 177 829 -114 -343 0 2508 2503 2500 2516 1885 216 1121 388 1919 1157 365 1513 54 50 1963 588 1783 2037 2044 1424 174 1412 1414 0\n2518 -150 52 177 -111 88 152 -114 -343 0 2500 2508 2503 385 1935 1418 50 1990 596 1963 588 564 904 1984 589 2516 1885 216 2517 193 1858 1901 222 225 1414 1826 1412 911 1424 0\n2519 -111 -121 -794 88 152 80 -114 -770 -298 0 2498 2403 2501 2359 2021 2504 2356 2508 2368 2505 2509 388 1938 862 1513 50 1163 1932 358 1918 364 163 385 1595 1948 563 1509 1961 1978 574 1560 2383 582 1017 1823 1927 1923 558 357 1033 1957 1029 1559 698 1562 1926 587 1518 930 351 2518 1645 75 175 176 192 1681 1834 1893 1316 1888 218 1318 216 0\n2520 -168 161 97 69 -121 0 579 834 1952 1821 552 0\n2521 150 -112 -121 -122 13 151 -298 0 2356 2508 2403 2498 2504 394 386 1936 527 352 170 395 1920 1245 1997 1515 1932 358 1918 1081 1570 1761 1078 563 1509 1079 1961 1834 574 1888 1823 2384 1058 558 1957 573 698 1062 1057 2520 1649 176 593 1061 1954 831 612 1821 552 0\n2522 -112 -121 -122 13 151 15 187 -298 0 2503 2021 2403 2506 2350 2499 394 1943 1341 395 1920 366 1515 65 1932 358 170 386 2521 909 1826 396 1522 1925 372 1556 1173 459 1951 1995 1033 551 1604 1029 593 1533 842 911 1562 1954 745 934 1343 597 1337 1828 2397 936 1765 1340 1531 0\n2523 -121 -114 -770 -778 0 2498 2356 2359 2369 2021 2515 395 1920 1245 1997 366 1515 62 862 1513 52 48 1163 1990 596 1198 1932 358 1918 1081 394 1943 354 2519 2522 1052 1610 1511 1570 1761 1078 563 1509 1079 1961 1978 1855 574 1306 1017 1049 1823 1295 1923 1048 558 1033 1054 1957 1029 1953 1559 1036 1562 606 1926 1518 551 351 1668 1669 823 350 1506 1820 1921 367 0\n2524 -114 -770 -778 0 2498 2478 2348 2354 1198 1932 358 52 388 862 1938 359 2515 62 395 2523 1822 594 1960 1355 1999 1692 357 852 1927 374 483 1823 1010 558 633 0\n2525 162 98 -122 13 125 -185 77 0 2507 2504 2354 2508 2403 2505 2477 2502 2498 2510 2360 395 1920 1245 1997 366 1515 594 1960 1355 1999 751 552 1504 1823 2384 558 1957 632 633 573 640 579 1010 593 1908 1930 438 1649 352 531 363 170 1821 357 1698 833 952 152 0\n2526 -78 271 -185 370 -778 0 2358 2364 1198 594 1960 1553 1905 412 353 1988 41 359 1500 1913 1938 425 380 1020 385 309 1199 214 839 1830 10 585 553 616 0\n2527 -122 13 -185 370 -778 0 2348 1198 1932 594 1960 1553 430 398 1355 1999 1504 358 395 1944 360 2526 1692 357 852 1927 2525 374 0\n2528 122 -770 -778 0 2356 2524 1163 1963 1127 1198 1918 1081 1578 1613 1120 1511 1121 1570 1889 1078 1893 1079 0\n2529 -185 -770 -778 0 2478 2356 2528 395 1920 1554 1964 1944 360 65 1163 1963 588 1198 1932 358 594 1504 1960 1355 1999 2527 33 2526 1692 357 1927 1275 1998 1666 581 771 2162 599 553 1665 0\n2530 6 134 105 169 70 0 2364 10 0\n2531 121 185 0 2478 1822 0\n2532 142 14 170 106 78 0 2366 37 0\n2533 58 186 122 80 0 2479 1824 0\n2534 107 22 171 150 86 0 2368 75 0\n2535 52 31 159 95 0 2508 2505 119 0\n2536 102 38 0 2356 1829 0\n2537 61 104 125 168 0 2360 2510 152 0\n2538 206 -230 0 2352 247 0\n2539 222 -230 0 2349 273 0\n2540 -239 -242 0 2358 309 0\n2541 -239 -244 0 2355 310 0\n2542 -325 327 0 2504 612 0\n2543 -341 343 0 2504 651 0\n2544 354 -370 0 2504 699 0\n2545 -376 360 0 2504 701 0\n2546 -369 -324 0 2506 727 0\n2547 -332 -370 0 2506 731 0\n2548 -376 -380 0 2506 745 0\n2549 -325 -377 0 2507 751 0\n2550 -379 -341 0 2507 759 0\n2551 102 38 0 2356 791 0\n2552 -132 -97 0 2348 821 0\n2553 -114 -13 0 2498 862 0\n2554 -51 -85 0 2498 894 0\n2555 -104 -188 0 2348 921 0\n2556 -124 -168 0 2348 922 0\n2557 296 360 0 2354 1010 0\n2558 299 363 0 2359 1017 0\n2559 364 300 0 2355 1018 0\n2560 244 308 0 2506 1022 0\n2561 725 724 0 2021 1029 0\n2562 94 -724 0 2347 1034 0\n2563 -735 58 0 2478 1066 0\n2564 -746 150 0 2356 1570 0\n2565 751 752 0 2361 1101 0\n2566 102 104 -751 0 2501 1106 0\n2567 -768 31 22 30 38 23 0 2499 1155 0\n2568 87 -769 111 0 2477 2501 1592 0\n2569 -772 96 94 95 0 2347 1174 0\n2570 -772 112 96 120 0 2502 2347 1600 0\n2571 158 -773 184 160 0 2503 1602 0\n2572 -773 160 184 176 0 2503 1604 0\n2573 779 778 0 2367 1195 0\n2574 -780 51 59 50 49 58 0 2478 1213 0\n2575 112 -793 111 87 85 88 0 2477 1632 0\n2576 112 120 104 88 -793 0 2505 2477 1639 0\n2577 175 176 151 152 -794 149 0 2403 1642 0\n2578 184 150 149 152 -794 0 2508 2503 1644 0\n2579 184 150 152 -794 168 0 2508 2356 1645 0\n2580 184 176 -794 149 152 0 2403 2503 2508 1647 0\n2581 184 176 -794 168 152 0 2403 2508 1649 0\n2582 104 102 98 97 -799 0 2501 1276 0\n2583 134 184 162 -800 168 178 0 2356 1661 0\n2584 134 190 162 186 -800 178 0 2356 1665 0\n2585 802 803 0 2369 1295 0\n2586 804 805 0 2509 1316 0\n2587 807 808 0 2511 1325 0\n2588 61 59 58 -807 60 0 2478 1327 0\n2589 7 -810 47 15 23 31 0 2499 1340 0\n2590 827 826 0 2363 1394 0\n2591 -826 107 111 112 106 105 0 2477 1401 0\n2592 -826 112 76 120 68 80 88 0 2477 2505 1729 0\n2593 -826 124 76 68 0 2477 2505 1730 0\n2594 -827 132 188 179 170 186 171 131 178 187 0 2508 2403 1732 0\n2595 52 51 49 56 50 -828 0 2500 1414 0\n2596 -830 188 132 131 178 179 133 186 187 0 2503 2508 2510 1741 0\n2597 -831 59 30 62 58 38 0 2478 1745 0\n2598 389 102 0 2350 1765 0\n2599 -111 -178 170 -778 106 0 2366 1774 0\n2600 342 -748 151 95 -770 0 2359 1792 0\n2601 -124 184 0 2356 2348 2016 0\n2602 96 747 -158 159 95 188 0 2348 2022 0\n2603 -135 120 0 2478 2047 0\n2604 52 31 -178 51 215 38 0 2501 2508 2477 2103 0\n2605 -325 -354 0 2507 2478 2115 0\n2606 810 -376 369 0 2478 2128 0\n2607 -326 -362 378 0 2478 2162 0\n2608 -769 102 86 186 756 0 2501 2169 0\n2609 -327 -370 0 2478 2192 0\n2610 -86 178 186 0 2367 2244 0\n2611 22 158 141 38 133 150 -111 30 -370 170 149 14 -779 0 2478 2293 0\n2612 -112 -86 -779 -186 106 0 2364 2366 2478 2296 0\n2613 -168 354 270 98 -121 13 318 0 2501 2383 0\n2614 188 132 77 -102 186 0 2506 2403 2397 0\n2615 -324 175 149 363 -122 0 2508 2503 2478 2411 0\n2616 120 -793 85 -186 0 2505 2477 2502 2478 2457 0\n2617 -793 -186 85 86 0 2502 2505 2458 0\n2618 -800 162 378 186 178 0 1666 581 771 2607 599 553 2584 0\n2619 342 168 -794 152 114 758 278 0 564 1000 2579 1840 176 1891 1577 1121 1120 0\n2620 242 134 170 168 -121 -122 114 370 0 394 395 1920 1245 1997 1515 1127 1121 1020 1120 1938 1577 359 176 393 2581 2579 1942 876 840 1511 528 2532 353 559 1501 1958 2530 580 0\n2621 326 168 -121 -122 114 187 370 -298 0 1918 1127 1515 395 1920 1245 1997 2619 1984 589 1962 581 1554 1950 550 65 588 1932 358 1081 553 2620 1889 1890 1891 1893 1894 185 2538 1079 206 1078 2536 2564 377 83 1511 1928 1674 2559 2585 715 1298 1558 1923 452 1004 359 996 606 2532 1958 551 1501 580 714 2614 1557 597 451 2548 353 593 2530 2581 840 0\n2622 168 -121 -122 114 187 370 -298 0 395 1920 1245 1997 1515 1127 2621 1953 1982 586 2581 176 593 881 842 1577 2606 1120 1121 1857 1865 2540 193 200 214 2589 0\n2623 -242 188 133 5 -313 131 186 187 178 -298 0 1932 358 1918 1081 1889 1891 1893 2538 1079 1000 206 1078 1962 1984 2536 2564 581 589 377 2614 83 551 2552 1674 1951 1970 2585 1556 573 1298 1925 1821 473 525 352 408 0\n2624 -102 262 -168 -121 186 77 0 579 1975 597 377 2614 409 551 2552 352 1970 2520 573 0\n2625 -149 318 270 13 -168 -121 0 563 1509 1961 2613 0\n2626 -150 170 -770 -778 0 2528 1515 2524 1163 1963 1127 1198 588 1990 596 65 395 1920 1554 1950 550 2529 2531 394 2622 834 579 1952 552 1975 597 2623 1121 1120 1577 176 1245 1997 866 1020 1938 393 1942 2625 2580 170 1932 358 528 2624 2551 206 1895 1413 2598 1532 1943 354 83 564 1511 1984 589 1674 2585 1298 1923 1033 2561 1036 1967 2615 551 2596 1610 1412 385 1418 1935 0\n2627 -770 -778 0 1198 1163 1963 1990 588 1127 596 2524 2528 65 395 1515 1920 1554 1245 1997 2529 1950 2531 550 394 2622 579 866 834 1952 1975 552 597 2623 1121 1020 1120 1938 1577 176 393 1942 2625 2578 564 2626 1962 581 0\n2628 -168 370 133 178 -150 188 179 187 -122 -778 0 395 1920 1554 1950 550 83 1680 2585 1298 1923 1033 2561 1562 1511 366 1515 65 2627 1198 2556 866 2527 2531 394 834 1943 2623 354 217 1885 1020 216 1919 1157 1152 1153 1858 1901 222 225 1826 396 1522 1925 372 1556 1828 1951 934 551 1610 2596 385 904 930 1935 2595 1418 1412 0\n2629 -121 370 133 178 -150 188 149 187 -122 -778 0 2371 2628 395 1920 1554 1950 550 83 1680 2585 1298 1923 1033 2561 1036 1967 1562 1511 65 2627 1198 394 2622 1943 48 50 388 1513 2553 354 1919 2522 1157 1610 1152 163 385 904 930 1153 2615 1935 1856 1858 551 1418 216 222 2596 1412 2595 0\n2630 370 133 178 -150 188 149 187 -122 -778 0 395 1920 1554 1964 1944 360 65 62 1198 1932 358 2629 2531 594 2527 2526 1960 33 1355 2618 1999 1998 1692 1275 357 1927 0\n2631 -370 178 -150 362 188 149 187 -122 0 395 1920 1554 1950 550 2371 83 1680 2585 1298 1923 1033 2561 1036 1967 1511 82 581 1245 1997 1944 1515 65 1963 1983 717 565 559 585 2615 2577 551 170 876 2594 2532 2590 359 1913 425 380 385 2591 0\n2632 178 -150 362 188 149 187 -122 -778 0 395 1920 1554 1950 550 2371 83 1680 2585 1298 1923 1033 2561 1036 581 1245 1997 1515 65 2631 2630 552 1952 2605 2549 579 2557 2545 1560 594 1930 593 1927 2531 397 2581 357 394 586 526 1953 351 606 2593 551 2590 2594 0\n2633 -150 362 188 149 187 -122 -778 0 581 395 1920 1245 1997 1515 1511 2632 588 2599 1963 1983 717 565 559 585 2577 795 876 871 2532 0\n2634 150 149 -122 745 0 395 1920 1245 1997 1515 2564 2578 1761 1078 176 565 1513 1079 1577 1963 1840 1127 1891 1120 1121 0\n2635 -188 -122 0 395 1920 1245 1997 1515 135 597 2555 1975 2548 579 1109 593 1268 2565 170 2566 1108 377 946 393 1941 2537 523 398 0\n2636 149 187 -122 -778 0 2635 1198 1918 1081 2634 564 2633 1962 0\n2637 -120 124 -158 379 187 -122 770 0 2635 395 1920 366 1515 393 445 1157 1152 1153 1901 225 1025 1826 1925 1522 372 462 1828 371 226 940 1902 2602 1088 0\n2638 184 -150 187 -122 -778 0 1511 2636 563 1978 2558 1923 1033 2561 1562 2550 395 1920 366 1515 2627 2601 2637 1831 222 1858 1153 1152 1157 1919 1945 388 396 1611 1826 909 0\n2639 -769 -184 85 187 -122 86 0 395 1920 366 1515 1157 1589 1945 913 396 1826 0\n2640 -150 187 -122 -778 0 2636 563 1961 1560 1927 357 2544 1127 588 1978 582 574 2550 1509 72 2635 395 1920 1554 1950 550 366 65 62 2627 1198 1932 358 1918 364 564 1962 1984 581 589 2638 176 881 2639 1152 1153 1857 1901 1121 1025 1120 1925 1577 1556 1513 2553 1951 2527 1823 551 2531 558 2594 1957 2590 1559 2522 2592 1926 351 0\n2641 143 769 87 23 151 51 -343 -184 0 2037 1783 0\n2642 187 -122 -778 0 395 1944 360 1920 366 1515 62 2627 1198 1932 358 1918 364 2636 72 563 1961 1978 2550 2543 1560 2544 582 2558 1927 1127 1923 357 1033 2561 1562 1518 2640 2534 192 1834 1840 1893 1888 1891 218 216 1121 1020 1120 1919 1938 365 1157 359 1693 1152 1999 1153 1355 1901 1960 225 1025 594 1826 1925 2531 1522 906 1173 394 1995 1943 2572 354 176 911 842 2603 1577 1751 1513 2641 0\n2643 -122 -778 0 395 1515 1920 1245 1997 2635 2642 596 1521 1969 2550 572 563 2413 1987 593 2601 2580 1828 586 933 674 2562 1036 2561 0\n2644 -176 -724 -187 124 0 1033 1940 2560 1894 2539 206 2536 377 1941 2562 596 1969 1179 1995 572 1521 170 933 946 2570 1828 393 597 2555 523 1975 398 579 2537 0\n2645 -724 -187 184 -778 0 596 2550 563 104 101 2601 2643 1198 1918 364 1033 2562 1923 1940 1517 382 2560 1894 2539 206 2536 377 436 363 2644 2580 1997 1631 365 1786 1919 1121 388 1889 1613 1893 1511 192 2534 0\n2646 -187 184 -778 0 103 104 596 1521 1969 2550 1179 563 1995 2645 2561 1036 1562 1967 674 115 1518 1306 586 2569 2585 2580 371 1997 1924 1245 389 1906 1672 350 0\n2647 -793 -725 -778 0 1036 1967 2558 1933 363 1306 2585 1562 1518 2643 1563 2627 1198 1918 364 1245 2617 1906 1564 350 1064 1065 1897 1901 1153 1152 1157 1589 1945 92 396 1672 0\n2648 -725 184 -778 0 2643 1563 2627 1198 1918 364 1036 1562 1967 1518 582 2558 1933 363 2647 1997 1257 1964 1069 1064 1065 1897 1901 1153 1152 1157 1589 1919 1786 388 1613 1511 2534 192 1121 1840 1891 0\n2649 -344 184 -778 0 1198 1918 2648 2561 1033 1940 2560 1894 2539 206 2536 377 436 363 1923 1298 2585 2562 1517 2646 2643 1563 2627 364 1950 1964 550 1069 1680 1064 94 1065 1589 1897 1152 1901 1153 0\n2650 184 -778 0 2643 1563 2627 1198 1918 364 2648 2561 1033 2562 1923 1940 1517 382 2560 1894 2539 206 2536 377 436 363 2649 1257 1997 2617 1564 1064 1065 1897 1901 1153 1152 1157 1589 1919 1786 388 1121 1613 1889 1511 1893 2534 192 0\n2651 -793 -778 0 2650 593 2548 597 1987 2643 1563 1198 1932 358 1918 364 1245 2647 449 2561 1028 1033 1904 1940 540 214 2560 1026 1894 1902 2539 200 206 2536 377 436 363 2617 1564 2614 1064 551 1065 2546 750 1897 1899 2606 594 1901 186 2531 193 842 2589 0\n2652 -778 0 1198 1918 364 1081 2627 2643 1563 2651 1997 1257 1964 595 1069 1064 1065 1897 1901 1153 1152 1157 1919 388 1124 1613 1511 2564 1078 1079 1840 1891 1121 1120 2608 1580 377 1512 436 1589 363 0\n2653 779 0 2652 2573 0\n2654 362 0 2653 1204 0\n2655 -342 0 2654 1962 0\n2656 -333 0 2654 1977 0\n2657 -150 0 2655 564 0\n2658 -746 0 2655 1084 0\n2659 -141 0 2656 558 0\n2660 -85 -794 0 2657 1257 1964 595 1950 550 72 363 1508 2554 1917 1933 1275 1298 2558 1998 2585 1967 2618 1036 56 588 2561 1963 2609 1033 2562 565 554 1940 1517 1761 1640 2560 1563 102 104 1894 2032 1582 1679 2539 200 1795 928 206 2604 0\n2661 -179 -724 215 -794 0 2657 2653 1033 1923 2558 1978 563 2562 1851 200 1153 193 2660 1257 1964 595 1950 91 94 96 589 1519 1593 1783 619 2535 1152 554 928 1589 1616 1510 0\n2662 -724 215 -794 0 2657 1257 1950 550 1033 2562 1923 1517 1298 2558 2585 1978 563 2661 1680 104 596 1640 1990 565 0\n2663 -187 -794 0 2657 104 596 1990 2550 565 563 1640 0\n2664 86 -769 -725 -794 0 2657 1157 1919 1124 1036 1967 582 1562 1518 2660 1257 1964 595 2534 1589 192 1512 1840 1580 1891 1120 1121 0\n2665 -769 -725 -794 0 2653 1257 1964 595 2664 1510 2610 588 1512 2609 2568 554 163 1616 0\n2666 -735 87 -757 47 243 142 -343 769 188 -158 747 23 0 2659 218 1065 2563 1897 59 334 222 1578 54 1513 2641 1781 1783 799 2602 2489 854 2531 1750 0\n2667 -184 87 -757 51 -343 769 23 0 176 1577 54 1513 2641 0\n2668 215 -794 0 2655 2653 2657 2659 2660 1257 1964 1069 595 666 193 1851 1153 1088 2662 2561 1036 1562 647 763 597 2665 1152 1163 1963 588 1127 2610 2233 1617 1567 1079 45 1840 1893 266 1891 218 214 1121 1020 1120 1919 1938 365 2666 1064 1563 2170 1515 2634 1961 1509 574 1283 1998 2667 2579 157 866 1823 2384 358 2582 420 377 0\n2669 184 -794 0 2657 1257 1950 550 1964 595 2663 1582 2668 1901 1131 1130 1133 1925 1173 1995 1069 1841 1899 1065 1064 1563 1515 225 1024 1920 366 1826 1522 1858 222 2578 799 2571 2572 563 393 1518 906 1978 1942 582 536 2534 364 0\n2670 -86 363 -794 0 2653 2669 176 2603 2668 1841 1899 224 1901 225 1857 217 1856 216 1257 1964 595 364 1510 1939 1616 1214 585 903 718 2574 1217 1210 0\n2671 -158 -794 0 2657 1257 1964 1069 2668 1841 1899 1065 1064 1563 1515 2663 1901 225 1024 1920 366 1826 2669 911 1950 550 595 1582 1131 1130 1133 1945 1157 365 1857 1121 2660 570 1518 1967 582 2670 1567 2534 2634 192 563 1893 1961 2543 218 2544 2667 1127 1120 0\n2672 -794 0 1257 1950 1964 550 1069 2663 2668 1841 1901 1899 225 1065 1024 1064 1920 1563 366 1515 1826 2671 1562 1766 2561 571 1033 2562 1968 1923 1517 589 1298 1680 2585 0\n2673 793 0 2672 1997 0\n2674 280 0 2673 1245 0\n2675 -259 0 2674 1906 0\n2676 -314 0 2674 1920 0\n2677 -67 0 2675 350 0\n2678 -122 0 2676 395 0\n2679 -736 0 2676 1067 0\n2680 -87 -831 62 -184 756 38 30 0 365 1512 913 1919 2597 1124 61 1120 1580 0\n2681 -184 38 47 -804 -22 299 -94 158 0 192 1840 1891 1121 217 1834 1888 216 1893 218 109 175 593 1318 1987 124 928 1439 1766 1830 1789 385 900 953 1948 496 1436 389 1427 2680 84 193 1841 1901 1899 225 224 2597 0\n2682 -23 184 50 49 51 -804 158 0 2676 2679 193 1841 1858 1901 1899 222 225 1065 1024 1318 799 1064 1964 124 910 1564 566 1766 1826 1514 0\n2683 -52 23 87 47 -22 299 -94 158 0 192 1840 1891 1121 1893 218 124 928 1766 1830 1789 385 900 84 496 389 0\n2684 -363 86 0 2657 2678 1967 1978 570 1036 563 2561 1033 2562 1923 1940 1517 382 1320 2560 2534 2586 1894 2541 192 2539 214 1834 1840 1893 206 1888 1891 218 216 217 1121 2288 2681 1786 2682 2683 1318 222 1858 1867 1153 200 1152 2604 1157 1579 1919 1120 1124 0\n2685 87 86 0 2657 2658 2679 2673 2677 2655 2684 2558 1933 363 2617 1564 1064 1065 1898 1902 1088 1897 1901 1153 193 1567 1078 1079 1840 1891 1121 1893 1211 218 582 1923 1033 2561 1562 1518 2534 1306 2585 1589 1631 1152 100 1672 1789 1773 901 1781 2600 1574 1087 0\n2686 86 0 2677 2684 1306 2558 2585 1923 1033 2561 1562 1518 2685 92 365 1672 1945 396 0\n2687 -22 0 2686 77 0\n2688 -107 0 2686 79 0\n2689 278 0 2686 364 0\n2690 -170 0 2686 1510 0\n2691 -298 0 2689 1918 0\n2692 -307 0 2689 1939 0\n2693 -106 0 2691 381 0\n2694 -115 0 2692 389 0\n2695 -186 -184 0 2693 2686 2653 2673 2659 593 1954 2542 552 2548 1987 176 595 1514 2616 2612 1989 756 754 363 1508 2576 560 559 557 1917 379 865 1750 374 1908 1823 2384 2531 352 1498 833 1821 0\n2696 -184 0 2686 2653 2690 2679 176 2603 2695 1564 2610 1616 1064 588 1512 163 1065 1963 2568 1897 1163 1152 1901 1153 0\n2697 -124 0 2696 2601 0\n2698 186 80 135 770 87 0 2653 2690 2678 1616 2533 163 224 2568 1897 1152 1901 1153 0\n2699 -768 50 350 51 0 2696 2687 1036 2561 1033 1940 2560 1894 2539 206 1320 2586 2562 109 570 1153 1856 1858 216 222 2682 1318 2567 120 0\n2700 -178 -85 51 0 2653 2687 2657 2690 2659 363 1933 2558 1967 1036 2561 1033 1940 2560 1894 2539 206 2562 109 570 1917 1560 2605 552 72 51 588 1512 1963 1163 2699 1152 2568 2611 869 0\n2701 -85 88 51 0 2690 2693 2653 2686 2696 2673 363 1508 1917 1933 1275 2558 1998 1967 1036 2561 1033 2562 1940 2560 1894 2539 206 2536 377 1941 2700 2610 1615 61 2612 586 908 933 946 1953 2588 553 2587 2583 1331 157 523 2576 393 0\n2702 178 85 88 0 2690 2653 2696 2673 2686 2692 2688 2694 2677 2697 2610 1615 595 2616 908 1964 393 566 521 396 1672 1826 2585 2644 1306 2561 1967 1036 0\n2703 85 88 0 2697 2686 2690 2653 2692 2679 2673 2693 2659 2702 49 56 588 1512 1963 1983 2609 2547 1163 559 554 1343 557 1750 2531 1504 2698 61 595 2616 2612 2563 1964 393 841 2575 1064 566 1910 521 161 163 1341 396 1614 1337 908 1826 910 2438 2589 0\n2704 88 51 0 2701 2703 0\n2705 186 0 2686 2679 1564 2610 1064 588 1512 2563 1963 2609 58 1163 554 2698 0\n2706 -88 0 2705 1514 0\n2707 51 0 2706 2704 0\n2708 85 0 2706 2703 0\n2709 0 2707 2708 2554 0\n"

theorem raw_n8_b7_p000 (word:Fin 8→Fin 3) (base val:Sat.Valuation)
 (h:ModuleOPG1808CNF.LexModel word (lexRot 8) lexPerm base)
 (heq:∀ i,i<OPG1808Cuts.selectorBase 8→(val i↔base i))
 (hc:OPG1808Cuts.CutModel (n:=8) 7 val)
 (hp:word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(0:Fin 3)∧True):False:=by
 have m:=h.toModel
 have bad:=cert_n8_b7_p000 (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 173) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 182) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 191) (val 192) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 201) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 210) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 219) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 228) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 237) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 246) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 255) (val 256) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 265) (val 266) (val 267) (val 268) (val 269) (val 270) (val 271) (val 272) (val 273) (val 274) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 283) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 292) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 301) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 310) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 319) (val 320) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 329) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 336) (val 337) (val 338) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 347) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 356) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 365) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 374) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 383) (val 384) (val 385) (val 386) (val 387) (val 388) (val 389) (val 390) (val 391) (val 392) (val 393) (val 394) (val 395) (val 396) (val 397) (val 398) (val 399) (val 400) (val 401) (val 402) (val 403) (val 404) (val 405) (val 406) (val 407) (val 408) (val 409) (val 410) (val 411) (val 412) (val 413) (val 414) (val 415) (val 416) (val 417) (val 418) (val 419) (val 420) (val 421) (val 422) (val 423) (val 424) (val 425) (val 426) (val 427) (val 428) (val 429) (val 430) (val 431) (val 432) (val 433) (val 434) (val 435) (val 436) (val 437) (val 438) (val 439) (val 440) (val 441) (val 442) (val 443) (val 444) (val 445) (val 446) (val 447) (val 448) (val 449) (val 450) (val 451) (val 452) (val 453) (val 454) (val 455) (val 456) (val 457) (val 458) (val 459) (val 460) (val 461) (val 462) (val 463) (val 464) (val 465) (val 466) (val 467) (val 468) (val 469) (val 470) (val 471) (val 472) (val 473) (val 474) (val 475) (val 476) (val 477) (val 478) (val 479) (val 480) (val 481) (val 482) (val 483) (val 484) (val 485) (val 486) (val 487) (val 488) (val 489) (val 490) (val 491) (val 492) (val 493) (val 494) (val 495) (val 496) (val 497) (val 498) (val 499) (val 500) (val 501) (val 502) (val 503) (val 504) (val 505) (val 506) (val 507) (val 508) (val 509) (val 510) (val 511) (val 512) (val 513) (val 514) (val 515) (val 516) (val 517) (val 518) (val 519) (val 520) (val 521) (val 522) (val 523) (val 524) (val 525) (val 526) (val 527) (val 528) (val 529) (val 530) (val 531) (val 532) (val 533) (val 534) (val 535) (val 536) (val 537) (val 538) (val 539) (val 540) (val 541) (val 542) (val 543) (val 544) (val 545) (val 546) (val 547) (val 548) (val 549) (val 550) (val 551) (val 552) (val 553) (val 554) (val 555) (val 556) (val 557) (val 558) (val 559) (val 560) (val 561) (val 562) (val 563) (val 564) (val 565) (val 566) (val 567) (val 568) (val 569) (val 570) (val 571) (val 572) (val 573) (val 574) (val 575) (val 576) (val 577) (val 578) (val 579) (val 580) (val 581) (val 582) (val 583) (val 584) (val 585) (val 586) (val 587) (val 588) (val 589) (val 590) (val 591) (val 592) (val 593) (val 594) (val 595) (val 596) (val 597) (val 598) (val 599) (val 600) (val 601) (val 602) (val 603) (val 604) (val 605) (val 606) (val 607) (val 608) (val 609) (val 610) (val 611) (val 612) (val 613) (val 614) (val 615) (val 616) (val 617) (val 618) (val 619) (val 620) (val 621) (val 622) (val 623) (val 624) (val 625) (val 626) (val 627) (val 628) (val 629) (val 630) (val 631) (val 632) (val 633) (val 634) (val 635) (val 636) (val 637) (val 638) (val 639) (val 640) (val 641) (val 642) (val 643) (val 644) (val 645) (val 646) (val 647) (val 648) (val 649) (val 650) (val 651) (val 652) (val 653) (val 654) (val 655) (val 656) (val 657) (val 658) (val 659) (val 660) (val 661) (val 662) (val 663) (val 664) (val 665) (val 666) (val 667) (val 668) (val 669) (val 670) (val 671) (val 672) (val 673) (val 674) (val 675) (val 676) (val 677) (val 678) (val 679) (val 680) (val 681) (val 682) (val 683) (val 684) (val 685) (val 686) (val 687) (val 688) (val 689) (val 690) (val 691) (val 692) (val 693) (val 694) (val 695) (val 696) (val 697) (val 698) (val 699) (val 700) (val 701) (val 702) (val 703) (val 704) (val 705) (val 706) (val 707) (val 708) (val 709) (val 710) (val 711) (val 712) (val 713) (val 714) (val 715) (val 716) (val 717) (val 718) (val 719) (val 720) (val 721) (val 722) (val 723) (val 724) (val 725) (val 726) (val 727) (val 728) (val 729) (val 730) (val 731) (val 732) (val 733) (val 734) (val 735) (val 736) (val 737) (val 738) (val 739) (val 740) (val 741) (val 742) (val 743) (val 744) (val 745) (val 746) (val 747) (val 748) (val 749) (val 750) (val 751) (val 752) (val 753) (val 754) (val 755) (val 756) (val 757) (val 758) (val 759) (val 760) (val 761) (val 762) (val 763) (val 764) (val 765) (val 766) (val 767) (val 768) (val 769) (val 770) (val 771) (val 772) (val 773) (val 774) (val 775) (val 776) (val 777) (val 778) (val 779) (val 780) (val 781) (val 782) (val 783) (val 784) (val 785) (val 786) (val 787) (val 788) (val 789) (val 790) (val 791) (val 792) (val 793) (val 794) (val 795) (val 796) (val 797) (val 798) (val 799) (val 800) (val 801) (val 802) (val 803) (val 804) (val 805) (val 806) (val 807) (val 808) (val 809) (val 810) (val 811) (val 812) (val 813) (val 814) (val 815) (val 816) (val 817) (val 818) (val 819) (val 820) (val 821) (val 822) (val 823) (val 824) (val 825) (val 826) (val 827) (val 828) (val 829) (val 830) (val 831) (val 832)
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
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 3 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 3 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 5 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 0 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 0 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 0 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 0 6 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 0 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 0 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 0 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 2 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 1 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 1 4 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 4 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 1 5 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 5 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 1 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 1 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 6 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 1 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 7 1 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 1 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 1 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 1 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 1 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 1 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 3 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 4 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 4 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 2 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 2 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 2 (by decide)) (by decide)) (b.1) (b.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 2 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 2 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 7 2 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 2 7 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 2 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 2 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 2 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 4 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 4 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 3 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 5 3 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 5 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 5 3 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 3 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 3 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 3 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 3 7 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 7 3 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 3 7 (by decide)) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 5 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 5 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 6 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 4 6 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 6 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 6 4 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 4 6 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 6 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 4 6 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 4 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 7 4 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 4 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 4 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 4 7 (by decide)) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
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
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 0 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 5 7 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 1 7 5 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 0 2 7 5 (by decide)) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 1 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 1 2 7 5 (by decide)) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.opposites_clause 2 2 5 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.orientation_clause 6 7 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 1 6 7 (by decide)) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 0 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.colors_clause 1 2 6 7 (by decide)) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 1) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 6) (by decide)) (b.1) (b.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 5) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 6) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 2 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 1) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 0) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 2) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 4 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 1) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 2) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 4) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 0) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 3) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 6 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 2) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 0 7 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 0 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 0 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 6) (by decide)) (b.1) (b.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 1 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 1) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 6) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 2 7) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 6) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 3) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 4 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 2) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 0) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 6 7) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 5) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 1 7 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 0 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
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
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 1 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 3) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 0 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 0) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 1 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 0) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 1) (by decide)) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 5) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 2 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 0) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 5) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 6) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 3 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 0) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 3) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 4 7) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 2) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 3) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 4) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 6) (by decide)) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 5 7) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 0) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 1) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 2) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 3) (by decide)) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 4) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 5) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 6 7) (by decide)) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 0) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 1) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 2) (by decide)) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 3) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 4) (by decide)) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 5) (by decide)) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.arc_reach_clause 2 7 6) (by decide)) (b.1) (b.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 0 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 3 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 6) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 3) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 1 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 0 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 4 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 2 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 5 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 4) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 3 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 0) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 6) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 5 7) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 4 7 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 2 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 3 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 4) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 6 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 1) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 5 7 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 5) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 1 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 2 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 2) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 4 7) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 6 7 5) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 0 6) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 3) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 1 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 0) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 4) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 2 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 1) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 3 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 0) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 2) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 5) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 4 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 0) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 1) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 2) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 3) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.trans_clause 2 7 5 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 7) (by decide)) (b))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 7) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 0) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 0) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 0) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 1) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 1) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 1) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 2) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 2) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 2) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 3) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 3) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 3) (by decide)) (b)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 3) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 4) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 4) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 4) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 4) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 5) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 5) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 5) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 5) (by decide)) (b))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.cycle_options_clause 6) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 0 6) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 1 6) (by decide)) (b))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.predecessor_clause 2 6) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 0 (hp.1)) (by decide)) (b))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 1 (hp.2.1)) (by decide)) (b)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.color_unit_clause 0 2 (hp.2.2.1)) (by decide)) (b))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 0 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 0 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 1 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 1 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 2 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 3 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 2 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 0 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 4 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 1 2 0 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (m.rainbow_clause 2 1 0 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 0 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 0 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 0 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 0 2 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 2 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 2 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 0 3 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 3 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 0 4 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 4 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 0 5 2 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 19 0 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 19 0 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 19 1 0 1 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 19 2 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 19 2 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 19 3 1 1 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 32 0 2 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 0 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 1 0 2 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 2 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 32 3 1 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 3 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 32 4 2 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 35 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 35 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 35 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 35 2 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.first_advance_clause 41 0 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 0 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 1 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 2 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 2 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 3 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 3 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.advance_clause 41 4 0 0 (by decide) (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 4 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(OPG1808Cuts.satisfies_of_below' heq (h.conflict_clause 41 5 1 0 (by decide)) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 0 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 1 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 1 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 1 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 2 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 2 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 3 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 3 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 4 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 4 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 5 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 5 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 6 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 6 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 6 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 2 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 3 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.ambient_clause 7 4 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 5 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.ambient_clause 7 6 (by decide) (by decide)) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 3) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 0 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 3 0 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 0 (by decide) 3 1 1) (b.1) (b.2.1) (b.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 3 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 4 0 0) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 4 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 5) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 5 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 5 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 1 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 5 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 5 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 0 (by decide) 6) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 6 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 6 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 6 2 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 0 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 0 (by decide) 7 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 0 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 0 (by decide) 7 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 0 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 1) (b.1) (b.2.1) (b.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 1 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 1 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 1 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 3 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 3 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 3 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 4 0) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 4 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 5) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 5 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 1 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 6 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 6 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.selector_clause 1 (by decide) 7) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.reach_clause 1 (by decide) 7 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 1 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 1 (by decide) 7 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 1 (by decide) 7 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 0) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 0 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 0 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 0 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 0 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 0 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 1 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 1 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 2 (by decide) 2) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 2 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 3 0) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 3 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 3 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 4) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 4 0) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 4 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 4 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 4 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 5 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 2 (by decide) 5 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 2 (by decide) 6) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 6 2) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 6 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 2 (by decide) 7) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>(hc.reach_clause 2 (by decide) 7 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 2 (by decide) 7 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 2 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 2 (by decide) 7 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 0 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 0 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 0 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 1) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 0 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 1 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 1 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 2 0) (b.1) (b.2))
 (fun b=>(hc.reach_clause 3 (by decide) 2 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 2 2) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 2 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 3) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 3 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 3 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 3 (by decide) 4) (b.1) (b.2.1) (b.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 4 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 3 (by decide) 5 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 5 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 5 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>(hc.selector_clause 3 (by decide) 6) (b.1) (b.2.1) (b.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 6 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 6 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 6 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 3 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 0 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 3 (by decide) 7 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 3 (by decide) 7 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 0) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 0) (b.1) (b.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 0 1) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 0 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 0 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 1) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 1 1) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 9) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 22) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 1 25) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 1 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 5) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 10) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 18) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 21) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 26) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 1 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 2) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 2 0) (b.1) (b.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 2 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 2 2) (b.1) (b.2))
 (fun b=>(hc.selector_clause 4 (by decide) 4) (b.1) (b.2.1) (b.2.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 0) (b.1) (b.2))
 (fun b=>(hc.reach_clause 4 (by decide) 4 1) (b.1) (b.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 4 2) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 4) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 8) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 11) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 12) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 13) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 17) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 4 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 5) (b.1) (b.2.1) (b.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 0) (b.1) (b.2))))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 0 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 5 1) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 1 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 5 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 6) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 7) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 20) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 23) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 27) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 5 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.selector_clause 4 (by decide) 6) (b.1) (b.2.1) (b.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 6 0) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 29) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 1) (b.1) (b.2)))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2)))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 2) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 1 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.reach_clause 4 (by decide) 6 2) (b.1) (b.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 3) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 6 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.selector_clause 4 (by decide) 7) (b.1) (b.2.1) (b.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 0) (b.1) (b.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 14) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 16) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 24) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 28) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2.2.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 30) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 0 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))
 (fun b=>Or.elim b
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 1) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 0) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 1 1) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))))
 (fun b=>Or.elim b
 (fun b=>(hc.reach_clause 4 (by decide) 7 2) (b.1) (b.2))
 (fun b=>Or.elim b
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 15) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.1) (b.2.2.2.2.2.2.2.2.2.2))
 (fun b=>(hc.cut_clause 4 (by decide) 7 2 31) (b.1) (b.2.1) (b.2.2.1) (b.2.2.2.1) (b.2.2.2.2.1) (b.2.2.2.2.2.1) (b.2.2.2.2.2.2)))))))))))))
end OPG1808CutCertificates
end

end Cut8Prefix000Packet

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
    (hprefix2 : color (2:Fin 8) (finRotate 8 (2:Fin 8)) = (0:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  exact Cut8Prefix000Packet.OPG1808PhysicalPrefix.predecessor_reachable_of_cut_exclusion
    (fun word ↦ word (0:Fin 8)=(0:Fin 3)∧word (1:Fin 8)=(0:Fin 3)∧word (2:Fin 8)=(0:Fin 3)∧True) Cut8Prefix000Packet.OPG1808CutCertificates.raw_n8_b7_p000
    D color htournament hnoRainbow hcycle hminimal ⟨hprefix0,hprefix1,hprefix2,True.intro⟩
