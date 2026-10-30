-- Prove2me | solution 1 for OPG1808.order_seven
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:08:13.99601+00:00
-- url     : https://prove2.me/submissions/5ed84de3-6614-4986-b3ab-e141e28d7fab

import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.PiLex

-- Bundled whole source: ModuleRUP.lean
namespace ModuleOPG1808Certificate

def ClauseProof (H : Sat.Valuation → Prop) (c : Sat.Clause) : Prop :=
  ∀ val : Sat.Valuation, H val → Sat.Valuation.satisfies val c

end ModuleOPG1808Certificate

-- Bundled whole source: ModuleCNF.lean





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

-- Bundled whole source: ModuleClauses.lean




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

-- Bundled whole source: ModuleLex.lean




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

-- Bundled whole source: ModuleTransforms.lean




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

-- Bundled whole source: PrefixTree.lean


namespace OPG1808PrefixTree

def PrefixAt (letters : ℕ → Fin 3) (start : ℕ) : List (Fin 3) → Prop
  | [] => True
  | c :: rest => letters start = c ∧ PrefixAt letters (start + 1) rest

def Prefix (letters : ℕ → Fin 3) (digits : List (Fin 3)) : Prop :=
  PrefixAt letters 0 digits

theorem prefixAt_append_digit (letters : ℕ → Fin 3) (start : ℕ)
    (digits : List (Fin 3)) (c : Fin 3) :
    PrefixAt letters start (digits ++ [c]) ↔
      PrefixAt letters start digits ∧ letters (start + digits.length) = c := by
  induction digits generalizing start with
  | nil => simp only [PrefixAt, List.nil_append, List.length_nil, Nat.add_zero, and_true, true_and]
  | cons d rest ih =>
    simp only [List.cons_append, PrefixAt, ih, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 rest.length, and_assoc]

def wordLetters {n : ℕ} [NeZero n] (word : Fin n → Fin 3) (i : ℕ) : Fin 3 :=
  word (Fin.ofNat n i)

def Excludes {n : ℕ} [NeZero n] [NeZero (n - 1)] (digits : List (Fin 3)) : Prop :=
  ∀ (word : Fin n → Fin 3) (val : Sat.Valuation),
    ModuleOPG1808CNF.LexModel word (ModuleOPG1808Certificate.lexRot n)
      ModuleOPG1808Certificate.lexPerm val → Prefix (wordLetters word) digits → False

/-- The children cover all three possible colors at the next exact position. -/
theorem split {n : ℕ} [NeZero n] [NeZero (n - 1)] (digits : List (Fin 3))
    (h0 : Excludes (n := n) (digits ++ [0]))
    (h1 : Excludes (n := n) (digits ++ [1]))
    (h2 : Excludes (n := n) (digits ++ [2])) : Excludes (n := n) digits := by
  intro word val hmodel hp
  rcases ModuleOPG1808CNF.fin3_cases (wordLetters word digits.length) with hc | hc | hc
  · exact h0 word val hmodel ((prefixAt_append_digit _ 0 digits 0).mpr
      ⟨hp, by simpa only [Nat.zero_add] using hc⟩)
  · exact h1 word val hmodel ((prefixAt_append_digit _ 0 digits 1).mpr
      ⟨hp, by simpa only [Nat.zero_add] using hc⟩)
  · exact h2 word val hmodel ((prefixAt_append_digit _ 0 digits 2).mpr
      ⟨hp, by simpa only [Nat.zero_add] using hc⟩)

theorem root_exclusion {n : ℕ} [NeZero n] [NeZero (n - 1)]
    (hroot : Excludes (n := n) []) (word : Fin n → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (ModuleOPG1808Certificate.lexRot n)
      ModuleOPG1808Certificate.lexPerm val) : False :=
  hroot word val h trivial

end OPG1808PrefixTree

-- Bundled whole source: LeafN3Root.lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OrdinaryLRATBridge
theorem satOne {v : Sat.Valuation} {c : Sat.Clause} (h : v.satisfies c) :
    v.satisfies_fmla (Sat.Fmla.one c) := by
  constructor
  intro d hd
  change d ∈ [c] at hd
  have heq : d = c := List.mem_singleton.mp hd
  subst d
  exact h

theorem satAnd {v : Sat.Valuation} {f g : Sat.Fmla}
    (hf : v.satisfies_fmla f) (hg : v.satisfies_fmla g) :
    v.satisfies_fmla (Sat.Fmla.and f g) := by
  constructor
  intro c hc
  change c ∈ f ++ g at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hf.prop c hc
  · exact hg.prop c hc
end OrdinaryLRATBridge

namespace OPG1808SmallOrders
open ModuleOPG1808Certificate OrdinaryLRATBridge

theorem input_n3_c0 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.pos 2, Sat.Literal.pos 6, Sat.Literal.pos 11, Sat.Literal.pos 15, Sat.Literal.pos 20, Sat.Literal.pos 24] :=
  h.toModel.orientation_clause (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n3_c1 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.pos 5, Sat.Literal.pos 7, Sat.Literal.pos 14, Sat.Literal.pos 16, Sat.Literal.pos 23, Sat.Literal.pos 25] :=
  h.toModel.orientation_clause (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n3_c2 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.pos 28] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 3) (1 : Fin 3)

theorem input_n3_c3 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.pos 29] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 3) (2 : Fin 3)

theorem input_n3_c4 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.pos 32] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)

theorem input_n3_c5 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 6, Sat.Literal.pos 33] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 3)

theorem input_n3_c6 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.pos 34] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)

theorem input_n3_c7 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.neg 32, Sat.Literal.pos 29] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)

theorem input_n3_c8 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 28, Sat.Literal.pos 34] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

theorem input_n3_c9 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.pos 38] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)

theorem input_n3_c10 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 14, Sat.Literal.pos 41] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 3) (2 : Fin 3)

theorem input_n3_c11 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.pos 42] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3)

theorem input_n3_c12 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 16, Sat.Literal.pos 43] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 3)

theorem input_n3_c13 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 41, Sat.Literal.neg 42, Sat.Literal.pos 39] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3)

theorem input_n3_c14 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 20, Sat.Literal.pos 47] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 3) (2 : Fin 3)

theorem input_n3_c15 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.pos 52] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 3) (1 : Fin 3)

theorem input_n3_c16 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29] :=
  h.toModel.predecessor_clause (0 : Fin 3) (2 : Fin 3)

theorem input_n3_c17 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38] :=
  h.toModel.predecessor_clause (1 : Fin 3) (2 : Fin 3)

theorem input_n3_c18 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 47] :=
  h.toModel.predecessor_clause (2 : Fin 3) (2 : Fin 3)

theorem input_n3_c19 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.pos 1, Sat.Literal.pos 10, Sat.Literal.pos 19] :=
  h.toModel.cycle_options_clause (0 : Fin 3)

theorem input_n3_c20 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39] :=
  h.toModel.predecessor_clause (1 : Fin 3) (0 : Fin 3)

theorem input_n3_c21 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34] :=
  h.toModel.predecessor_clause (0 : Fin 3) (1 : Fin 3)

theorem input_n3_c22 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 43] :=
  h.toModel.predecessor_clause (1 : Fin 3) (1 : Fin 3)

theorem input_n3_c23 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52] :=
  h.toModel.predecessor_clause (2 : Fin 3) (1 : Fin 3)

theorem input_n3_c24 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 14, Sat.Literal.neg 24] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n3_c25 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 1, Sat.Literal.pos 54] :=
  h.first_advance_clause 0 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n3_c26 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 19] :=
  h.first_conflict_clause 0 (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n3_c27 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.neg 23, Sat.Literal.neg 23] :=
  h.conflict_clause 0 (0 : Fin 2) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n3_c28 (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 10] :=
  h.first_conflict_clause 1 (1 : Fin 3) (1 : Fin 3) (by decide)

lrat_proof cert_n3_root
  "p cnf 88 29\n3 7 12 16 21 25 0\n6 8 15 17 24 26 0\n-2 29 0\n-3 30 0\n-6 33 0\n-7 34 0\n-8 35 0\n-29 -33 30 0\n-34 -29 35 0\n-12 39 0\n-15 42 0\n-16 43 0\n-17 44 0\n-42 -43 40 0\n-21 48 0\n-26 53 0\n-30 0\n-39 0\n-48 0\n2 11 20 0\n-40 0\n-35 0\n-44 0\n-53 0\n-2 -15 -25 0\n-2 -2 55 0\n-20 -20 0\n-55 -24 -24 0\n-11 -11 0\n"
  "30 -3 0 17 4 0\n31 -12 0 18 10 0\n32 -21 0 19 15 0\n33 -8 0 22 7 0\n34 -17 0 23 13 0\n35 -26 0 24 16 0\n36 -2 55 0 26 0\n37 -20 0 27 0\n38 -55 -24 0 28 0\n39 -11 0 29 0\n40 2 0 39 37 20 0\n41 29 0 40 3 0\n42 55 0 40 36 0\n43 -33 0 41 17 8 0\n44 -34 0 41 22 9 0\n45 -24 0 42 38 0\n46 -6 0 43 5 0\n47 -7 0 44 6 0\n48 15 0 46 33 34 45 35 2 0\n49 42 0 48 11 0\n50 -25 0 48 40 25 0\n51 -43 0 49 21 14 0\n52 16 0 50 30 31 32 47 1 0\n53 0 52 51 12 0\n"

theorem raw_n3_root (word : Fin 3 → Fin 3) :
    ClauseProof (fun val => ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val ∧ True) Sat.Clause.nil := by
  intro val hh
  have h := hh.left
  have bad := cert_n3_root (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87)
  exact Or.elim (bad)
    (fun badL0 => Or.elim (badL0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => input_n3_c0 word val h (badL3.1) (badL3.2.1) (badL3.2.2.1) (badL3.2.2.2.1) (badL3.2.2.2.2.1) (badL3.2.2.2.2.2))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c1 word val h (badL4.1) (badL4.2.1) (badL4.2.2.1) (badL4.2.2.2.1) (badL4.2.2.2.2.1) (badL4.2.2.2.2.2))
    (fun badR4 => input_n3_c2 word val h (badR4.1) (badR4.2))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => input_n3_c3 word val h (badL4.1) (badL4.2))
    (fun badR4 => input_n3_c4 word val h (badR4.1) (badR4.2)))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c5 word val h (badL4.1) (badL4.2))
    (fun badR4 => input_n3_c6 word val h (badR4.1) (badR4.2)))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => input_n3_c7 word val h (badL3.1) (badL3.2.1) (badL3.2.2))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c8 word val h (badL4.1) (badL4.2.1) (badL4.2.2))
    (fun badR4 => input_n3_c9 word val h (badR4.1) (badR4.2))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => input_n3_c10 word val h (badL4.1) (badL4.2))
    (fun badR4 => input_n3_c11 word val h (badR4.1) (badR4.2)))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c12 word val h (badL4.1) (badL4.2))
    (fun badR4 => input_n3_c13 word val h (badR4.1) (badR4.2.1) (badR4.2.2))))))
    (fun badR0 => Or.elim (badR0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => input_n3_c14 word val h (badL3.1) (badL3.2))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c15 word val h (badL4.1) (badL4.2))
    (fun badR4 => input_n3_c16 word val h (badR4))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => input_n3_c17 word val h (badL4))
    (fun badR4 => input_n3_c18 word val h (badR4)))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c19 word val h (badL4.1) (badL4.2.1) (badL4.2.2))
    (fun badR4 => input_n3_c20 word val h (badR4)))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => input_n3_c21 word val h (badL4))
    (fun badR4 => input_n3_c22 word val h (badR4)))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c23 word val h (badL4))
    (fun badR4 => input_n3_c24 word val h (badR4.1) (badR4.2.1) (badR4.2.2))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => input_n3_c25 word val h (badL4.1) (badL4.2.1) (badL4.2.2))
    (fun badR4 => input_n3_c26 word val h (badR4.1) (badR4.2)))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => input_n3_c27 word val h (badL4.1) (badL4.2.1) (badL4.2.2))
    (fun badR4 => input_n3_c28 word val h (badR4.1) (badR4.2))))))

theorem exclude_n3_root (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) (_hp : True) : False :=
  raw_n3_root word val ⟨h, True.intro⟩

theorem universal_n3_root (word : Fin 3 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 3) lexPerm val) : False :=
  raw_n3_root word val ⟨h, True.intro⟩
end OPG1808SmallOrders


-- Bundled whole source: LeafN4Root.lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OPG1808SmallOrders
open ModuleOPG1808Certificate OrdinaryLRATBridge

theorem input_n4_c0 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 3, Sat.Literal.pos 12, Sat.Literal.pos 19, Sat.Literal.pos 28, Sat.Literal.pos 35, Sat.Literal.pos 44] :=
  h.toModel.orientation_clause (0 : Fin 4) (3 : Fin 4) (by decide)

theorem input_n4_c1 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 7, Sat.Literal.pos 13, Sat.Literal.pos 23, Sat.Literal.pos 29, Sat.Literal.pos 39, Sat.Literal.pos 45] :=
  h.toModel.orientation_clause (1 : Fin 4) (3 : Fin 4) (by decide)

theorem input_n4_c2 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 11, Sat.Literal.pos 14, Sat.Literal.pos 27, Sat.Literal.pos 30, Sat.Literal.pos 43, Sat.Literal.pos 46] :=
  h.toModel.orientation_clause (2 : Fin 4) (3 : Fin 4) (by decide)

theorem input_n4_c3 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.pos 49] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 4) (1 : Fin 4)

theorem input_n4_c4 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.pos 51] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 4) (3 : Fin 4)

theorem input_n4_c5 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 6, Sat.Literal.pos 54] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 4) (2 : Fin 4)

theorem input_n4_c6 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.pos 55] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 4) (3 : Fin 4)

theorem input_n4_c7 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.pos 59] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 4) (3 : Fin 4)

theorem input_n4_c8 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.pos 60] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 4) (0 : Fin 4)

theorem input_n4_c9 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 13, Sat.Literal.pos 61] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 4) (1 : Fin 4)

theorem input_n4_c10 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 14, Sat.Literal.pos 62] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 4) (2 : Fin 4)

theorem input_n4_c11 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 49, Sat.Literal.neg 54, Sat.Literal.pos 50] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)

theorem input_n4_c12 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 49, Sat.Literal.neg 55, Sat.Literal.pos 51] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4)

theorem input_n4_c13 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.neg 59, Sat.Literal.pos 55] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)

theorem input_n4_c14 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 61, Sat.Literal.pos 57] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)

theorem input_n4_c15 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 50, Sat.Literal.pos 62] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 4) (0 : Fin 4) (2 : Fin 4)

theorem input_n4_c16 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.neg 54, Sat.Literal.pos 62] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 4) (1 : Fin 4) (2 : Fin 4)

theorem input_n4_c17 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.pos 67] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 4) (3 : Fin 4)

theorem input_n4_c18 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.pos 70] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 4) (2 : Fin 4)

theorem input_n4_c19 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 23, Sat.Literal.pos 71] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 4) (3 : Fin 4)

theorem input_n4_c20 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 27, Sat.Literal.pos 75] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 4) (3 : Fin 4)

theorem input_n4_c21 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.pos 76] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 4) (0 : Fin 4)

theorem input_n4_c22 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.pos 77] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 4) (1 : Fin 4)

theorem input_n4_c23 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 30, Sat.Literal.pos 78] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 4) (2 : Fin 4)

theorem input_n4_c24 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 71, Sat.Literal.neg 76, Sat.Literal.pos 68] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 4) (3 : Fin 4) (0 : Fin 4)

theorem input_n4_c25 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 77, Sat.Literal.pos 73] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)

theorem input_n4_c26 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 77, Sat.Literal.neg 70, Sat.Literal.pos 78] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 4) (1 : Fin 4) (2 : Fin 4)

theorem input_n4_c27 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 35, Sat.Literal.pos 83] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 4) (3 : Fin 4)

theorem input_n4_c28 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.pos 87] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 4) (3 : Fin 4)

theorem input_n4_c29 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.pos 92] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 4) (0 : Fin 4)

theorem input_n4_c30 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.pos 94] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 4) (2 : Fin 4)

theorem input_n4_c31 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 87, Sat.Literal.neg 92, Sat.Literal.pos 84] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 4) (3 : Fin 4) (0 : Fin 4)

theorem input_n4_c32 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51] :=
  h.toModel.predecessor_clause (0 : Fin 3) (3 : Fin 4)

theorem input_n4_c33 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67] :=
  h.toModel.predecessor_clause (1 : Fin 3) (3 : Fin 4)

theorem input_n4_c34 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83] :=
  h.toModel.predecessor_clause (2 : Fin 3) (3 : Fin 4)

theorem input_n4_c35 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 1, Sat.Literal.pos 17, Sat.Literal.pos 33] :=
  h.toModel.cycle_options_clause (0 : Fin 4)

theorem input_n4_c36 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68] :=
  h.toModel.predecessor_clause (1 : Fin 3) (0 : Fin 4)

theorem input_n4_c37 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 84] :=
  h.toModel.predecessor_clause (2 : Fin 3) (0 : Fin 4)

theorem input_n4_c38 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 6, Sat.Literal.pos 22, Sat.Literal.pos 38] :=
  h.toModel.cycle_options_clause (1 : Fin 4)

theorem input_n4_c39 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 57] :=
  h.toModel.predecessor_clause (0 : Fin 3) (1 : Fin 4)

theorem input_n4_c40 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 73] :=
  h.toModel.predecessor_clause (1 : Fin 3) (1 : Fin 4)

theorem input_n4_c41 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.pos 11, Sat.Literal.pos 27, Sat.Literal.pos 43] :=
  h.toModel.cycle_options_clause (2 : Fin 4)

theorem input_n4_c42 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 62] :=
  h.toModel.predecessor_clause (0 : Fin 3) (2 : Fin 4)

theorem input_n4_c43 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 78] :=
  h.toModel.predecessor_clause (1 : Fin 3) (2 : Fin 4)

theorem input_n4_c44 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94] :=
  h.toModel.predecessor_clause (2 : Fin 3) (2 : Fin 4)

theorem input_n4_c45 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 23, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n4_c46 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 39, Sat.Literal.neg 28] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n4_c47 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 6, Sat.Literal.neg 27, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n4_c48 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.neg 11, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n4_c49 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 1, Sat.Literal.pos 96] :=
  h.first_advance_clause 0 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n4_c50 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 33] :=
  h.first_conflict_clause 0 (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n4_c51 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.neg 6, Sat.Literal.neg 6, Sat.Literal.pos 97] :=
  h.advance_clause 0 (0 : Fin 3) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n4_c52 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.neg 38, Sat.Literal.neg 38] :=
  h.conflict_clause 0 (0 : Fin 3) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n4_c53 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 97, Sat.Literal.neg 43, Sat.Literal.neg 43] :=
  h.conflict_clause 0 (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n4_c54 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 17] :=
  h.first_conflict_clause 1 (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n4_c55 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 22, Sat.Literal.pos 117] :=
  h.first_advance_clause 7 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n4_c56 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 22, Sat.Literal.neg 27] :=
  h.conflict_clause 7 (0 : Fin 3) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n4_c57 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 22, Sat.Literal.pos 123] :=
  h.first_advance_clause 9 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n4_c58 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 22, Sat.Literal.neg 43, Sat.Literal.pos 124] :=
  h.advance_clause 9 (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n4_c59 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 43, Sat.Literal.neg 28] :=
  h.conflict_clause 9 (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n4_c60 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 43, Sat.Literal.pos 138] :=
  h.first_advance_clause 14 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n4_c61 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 138, Sat.Literal.neg 22, Sat.Literal.neg 44] :=
  h.conflict_clause 14 (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n4_c62 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 12, Sat.Literal.pos 147] :=
  h.first_advance_clause 17 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n4_c63 (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) :
    val.satisfies [Sat.Literal.neg 147, Sat.Literal.neg 22, Sat.Literal.neg 1] :=
  h.conflict_clause 17 (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (by decide)

lrat_proof cert_n4_root
  "p cnf 165 64\n4 13 20 29 36 45 0\n8 14 24 30 40 46 0\n12 15 28 31 44 47 0\n-2 50 0\n-4 52 0\n-7 55 0\n-8 56 0\n-12 60 0\n-13 61 0\n-14 62 0\n-15 63 0\n-50 -55 51 0\n-50 -56 52 0\n-55 -60 56 0\n-60 -62 58 0\n-61 -51 63 0\n-62 -55 63 0\n-20 68 0\n-23 71 0\n-24 72 0\n-28 76 0\n-29 77 0\n-30 78 0\n-31 79 0\n-72 -77 69 0\n-76 -78 74 0\n-78 -71 79 0\n-36 84 0\n-40 88 0\n-45 93 0\n-47 95 0\n-88 -93 85 0\n-52 0\n-68 0\n-84 0\n2 18 34 0\n-69 0\n-85 0\n7 23 39 0\n-58 0\n-74 0\n12 28 44 0\n-63 0\n-79 0\n-95 0\n-2 -24 -45 0\n-2 -40 -29 0\n-7 -28 -46 0\n-23 -12 -46 0\n-2 -2 97 0\n-34 -34 0\n-97 -7 -7 98 0\n-97 -39 -39 0\n-98 -44 -44 0\n-18 -18 0\n-2 -23 118 0\n-118 -23 -28 0\n-2 -23 124 0\n-124 -23 -44 125 0\n-125 -44 -29 0\n-2 -44 139 0\n-139 -23 -45 0\n-2 -13 148 0\n-148 -23 -2 0\n"
  "65 -4 0 33 5 0\n66 -20 0 34 18 0\n67 -36 0 35 28 0\n68 -15 0 43 11 0\n69 -31 0 44 24 0\n70 -47 0 45 31 0\n71 -2 97 0 50 0\n72 -34 0 51 0\n73 -97 -7 98 0 52 0\n74 -97 -39 0 53 0\n75 -98 -44 0 54 0\n76 -18 0 55 0\n77 2 0 76 72 36 0\n78 50 0 77 4 0\n79 97 0 77 71 0\n80 -56 0 78 33 13 0\n81 -39 0 79 74 0\n82 -8 0 80 7 0\n83 -23 118 0 77 56 0\n84 -23 124 0 77 58 0\n85 -44 139 0 77 61 0\n86 -13 148 0 77 63 0\n87 -148 -23 0 77 64 0\n88 -29 14 46 30 0 77 37 82 22 47 25 2 20 0\n89 -12 -23 0 44 40 67 66 65 77 38 82 19 27 23 87 86 8 49 15 10 88 1 30 46 32 2 29 0\n90 -23 0 67 66 65 83 84 87 89 57 86 42 85 59 62 60 1 0\n91 7 0 90 81 39 0\n92 55 0 91 6 0\n93 98 0 91 79 73 0\n94 51 0 92 78 12 0\n95 -60 0 92 80 14 0\n96 -62 0 92 43 17 0\n97 -44 0 93 75 0\n98 -61 0 94 43 16 0\n99 -12 0 95 8 0\n100 -14 0 96 10 0\n101 28 0 97 68 69 99 70 3 0\n102 -13 0 98 9 0\n103 76 0 101 21 0\n104 -46 0 101 91 48 0\n105 -78 0 103 41 26 0\n106 -30 0 105 23 0\n107 -29 0 106 100 104 88 0\n108 45 0 107 65 66 67 102 1 0\n109 93 0 108 30 0\n110 -24 0 108 77 46 0\n111 -88 0 109 38 32 0\n112 40 0 110 82 106 100 104 2 0\n113 0 112 111 29 0\n"

theorem raw_n4_root (word : Fin 4 → Fin 3) :
    ClauseProof (fun val => ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val ∧ True) Sat.Clause.nil := by
  intro val hh
  have h := hh.left
  have bad := cert_n4_root (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164)
  exact Or.elim (bad)
    (fun badL0 => Or.elim (badL0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c0 word val h (badL5.1) (badL5.2.1) (badL5.2.2.1) (badL5.2.2.2.1) (badL5.2.2.2.2.1) (badL5.2.2.2.2.2))
    (fun badR5 => input_n4_c1 word val h (badR5.1) (badR5.2.1) (badR5.2.2.1) (badR5.2.2.2.1) (badR5.2.2.2.2.1) (badR5.2.2.2.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c2 word val h (badL5.1) (badL5.2.1) (badL5.2.2.1) (badL5.2.2.2.1) (badL5.2.2.2.2.1) (badL5.2.2.2.2.2))
    (fun badR5 => input_n4_c3 word val h (badR5.1) (badR5.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c4 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c5 word val h (badR5.1) (badR5.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c6 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c7 word val h (badR5.1) (badR5.2)))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c8 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c9 word val h (badR5.1) (badR5.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c10 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c11 word val h (badR5.1) (badR5.2.1) (badR5.2.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c12 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c13 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c14 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c15 word val h (badR5.1) (badR5.2.1) (badR5.2.2))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c16 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c17 word val h (badR5.1) (badR5.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c18 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c19 word val h (badR5.1) (badR5.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c20 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c21 word val h (badR5.1) (badR5.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c22 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c23 word val h (badR5.1) (badR5.2)))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c24 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c25 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c26 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c27 word val h (badR5.1) (badR5.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c28 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c29 word val h (badR5.1) (badR5.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c30 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c31 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))))))
    (fun badR0 => Or.elim (badR0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c32 word val h (badL5))
    (fun badR5 => input_n4_c33 word val h (badR5)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c34 word val h (badL5))
    (fun badR5 => input_n4_c35 word val h (badR5.1) (badR5.2.1) (badR5.2.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c36 word val h (badL5))
    (fun badR5 => input_n4_c37 word val h (badR5)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c38 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c39 word val h (badR5)))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c40 word val h (badL5))
    (fun badR5 => input_n4_c41 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c42 word val h (badL5))
    (fun badR5 => input_n4_c43 word val h (badR5))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c44 word val h (badL5))
    (fun badR5 => input_n4_c45 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c46 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c47 word val h (badR5.1) (badR5.2.1) (badR5.2.2))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c48 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c49 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c50 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c51 word val h (badR5.1) (badR5.2.1) (badR5.2.2.1) (badR5.2.2.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c52 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c53 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c54 word val h (badL5.1) (badL5.2))
    (fun badR5 => input_n4_c55 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c56 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c57 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c58 word val h (badL5.1) (badL5.2.1) (badL5.2.2.1) (badL5.2.2.2))
    (fun badR5 => input_n4_c59 word val h (badR5.1) (badR5.2.1) (badR5.2.2))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => input_n4_c60 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c61 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => input_n4_c62 word val h (badL5.1) (badL5.2.1) (badL5.2.2))
    (fun badR5 => input_n4_c63 word val h (badR5.1) (badR5.2.1) (badR5.2.2)))))))

theorem exclude_n4_root (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) (_hp : True) : False :=
  raw_n4_root word val ⟨h, True.intro⟩

theorem universal_n4_root (word : Fin 4 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 4) lexPerm val) : False :=
  raw_n4_root word val ⟨h, True.intro⟩
end OPG1808SmallOrders


-- Bundled whole source: LeafN5Root.lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OPG1808SmallOrders
open ModuleOPG1808Certificate OrdinaryLRATBridge

theorem input_n5_c0 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 3, Sat.Literal.pos 15, Sat.Literal.pos 28, Sat.Literal.pos 40, Sat.Literal.pos 53, Sat.Literal.pos 65] :=
  h.toModel.orientation_clause (0 : Fin 5) (3 : Fin 5) (by decide)

theorem input_n5_c1 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 4, Sat.Literal.pos 20, Sat.Literal.pos 29, Sat.Literal.pos 45, Sat.Literal.pos 54, Sat.Literal.pos 70] :=
  h.toModel.orientation_clause (0 : Fin 5) (4 : Fin 5) (by decide)

theorem input_n5_c2 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 7, Sat.Literal.pos 11, Sat.Literal.pos 32, Sat.Literal.pos 36, Sat.Literal.pos 57, Sat.Literal.pos 61] :=
  h.toModel.orientation_clause (1 : Fin 5) (2 : Fin 5) (by decide)

theorem input_n5_c3 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 8, Sat.Literal.pos 16, Sat.Literal.pos 33, Sat.Literal.pos 41, Sat.Literal.pos 58, Sat.Literal.pos 66] :=
  h.toModel.orientation_clause (1 : Fin 5) (3 : Fin 5) (by decide)

theorem input_n5_c4 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 9, Sat.Literal.pos 21, Sat.Literal.pos 34, Sat.Literal.pos 46, Sat.Literal.pos 59, Sat.Literal.pos 71] :=
  h.toModel.orientation_clause (1 : Fin 5) (4 : Fin 5) (by decide)

theorem input_n5_c5 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 13, Sat.Literal.pos 17, Sat.Literal.pos 38, Sat.Literal.pos 42, Sat.Literal.pos 63, Sat.Literal.pos 67] :=
  h.toModel.orientation_clause (2 : Fin 5) (3 : Fin 5) (by decide)

theorem input_n5_c6 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 14, Sat.Literal.pos 22, Sat.Literal.pos 39, Sat.Literal.pos 47, Sat.Literal.pos 64, Sat.Literal.pos 72] :=
  h.toModel.orientation_clause (2 : Fin 5) (4 : Fin 5) (by decide)

theorem input_n5_c7 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 19, Sat.Literal.pos 23, Sat.Literal.pos 44, Sat.Literal.pos 48, Sat.Literal.pos 69, Sat.Literal.pos 73] :=
  h.toModel.orientation_clause (3 : Fin 5) (4 : Fin 5) (by decide)

theorem input_n5_c8 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.pos 76] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 5) (1 : Fin 5)

theorem input_n5_c9 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.pos 79] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 5) (4 : Fin 5)

theorem input_n5_c10 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.pos 82] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c11 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.pos 83] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 5) (3 : Fin 5)

theorem input_n5_c12 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.pos 84] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 5) (4 : Fin 5)

theorem input_n5_c13 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.pos 86] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 5) (1 : Fin 5)

theorem input_n5_c14 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 13, Sat.Literal.pos 88] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 5) (3 : Fin 5)

theorem input_n5_c15 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 14, Sat.Literal.pos 89] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 5) (4 : Fin 5)

theorem input_n5_c16 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.pos 90] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c17 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 16, Sat.Literal.pos 91] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 5) (1 : Fin 5)

theorem input_n5_c18 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.pos 92] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 5) (2 : Fin 5)

theorem input_n5_c19 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.pos 94] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c20 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 20, Sat.Literal.pos 95] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 5) (0 : Fin 5)

theorem input_n5_c21 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 21, Sat.Literal.pos 96] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c22 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.pos 97] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c23 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 23, Sat.Literal.pos 98] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 5) (3 : Fin 5)

theorem input_n5_c24 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.neg 82, Sat.Literal.pos 77] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 5) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c25 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.neg 84, Sat.Literal.pos 79] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 5) (1 : Fin 5) (4 : Fin 5)

theorem input_n5_c26 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 88, Sat.Literal.pos 83] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5)

theorem input_n5_c27 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 89, Sat.Literal.pos 84] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 5) (2 : Fin 5) (4 : Fin 5)

theorem input_n5_c28 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.neg 94, Sat.Literal.pos 84] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 5) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c29 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 85, Sat.Literal.neg 76, Sat.Literal.pos 86] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 5) (0 : Fin 5) (1 : Fin 5)

theorem input_n5_c30 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.neg 90, Sat.Literal.pos 85] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 5) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c31 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.neg 91, Sat.Literal.pos 86] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 5) (3 : Fin 5) (1 : Fin 5)

theorem input_n5_c32 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 90, Sat.Literal.neg 77, Sat.Literal.pos 92] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 5) (0 : Fin 5) (2 : Fin 5)

theorem input_n5_c33 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 91, Sat.Literal.neg 82, Sat.Literal.pos 92] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 5) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c34 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.neg 97, Sat.Literal.pos 92] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 5) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c35 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 95, Sat.Literal.neg 76, Sat.Literal.pos 96] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 5) (0 : Fin 5) (1 : Fin 5)

theorem input_n5_c36 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.neg 82, Sat.Literal.pos 97] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 5) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c37 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.neg 83, Sat.Literal.pos 98] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 5) (1 : Fin 5) (3 : Fin 5)

theorem input_n5_c38 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 97, Sat.Literal.neg 88, Sat.Literal.pos 98] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 5) (2 : Fin 5) (3 : Fin 5)

theorem input_n5_c39 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.pos 103] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 5) (3 : Fin 5)

theorem input_n5_c40 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.pos 104] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 5) (4 : Fin 5)

theorem input_n5_c41 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 32, Sat.Literal.pos 107] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c42 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.pos 108] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 5) (3 : Fin 5)

theorem input_n5_c43 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34, Sat.Literal.pos 109] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 5) (4 : Fin 5)

theorem input_n5_c44 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.pos 111] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 5) (1 : Fin 5)

theorem input_n5_c45 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.pos 113] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 5) (3 : Fin 5)

theorem input_n5_c46 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.pos 114] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 5) (4 : Fin 5)

theorem input_n5_c47 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 40, Sat.Literal.pos 115] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c48 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 41, Sat.Literal.pos 116] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 5) (1 : Fin 5)

theorem input_n5_c49 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 42, Sat.Literal.pos 117] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 5) (2 : Fin 5)

theorem input_n5_c50 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.pos 119] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c51 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.pos 120] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 5) (0 : Fin 5)

theorem input_n5_c52 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.pos 121] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c53 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 47, Sat.Literal.pos 122] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c54 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 48, Sat.Literal.pos 123] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 5) (3 : Fin 5)

theorem input_n5_c55 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 103, Sat.Literal.neg 119, Sat.Literal.pos 104] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 5) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c56 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 115, Sat.Literal.pos 105] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 5) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c57 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 120, Sat.Literal.pos 105] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 5) (4 : Fin 5) (0 : Fin 5)

theorem input_n5_c58 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 113, Sat.Literal.neg 116, Sat.Literal.pos 111] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 5) (3 : Fin 5) (1 : Fin 5)

theorem input_n5_c59 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 114, Sat.Literal.neg 121, Sat.Literal.pos 111] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 5) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c60 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 107, Sat.Literal.pos 117] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 5) (1 : Fin 5) (2 : Fin 5)

theorem input_n5_c61 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 119, Sat.Literal.neg 121, Sat.Literal.pos 116] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 5) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c62 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 119, Sat.Literal.neg 122, Sat.Literal.pos 117] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 5) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c63 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 120, Sat.Literal.neg 103, Sat.Literal.pos 123] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 5) (0 : Fin 5) (3 : Fin 5)

theorem input_n5_c64 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 122, Sat.Literal.neg 113, Sat.Literal.pos 123] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 5) (2 : Fin 5) (3 : Fin 5)

theorem input_n5_c65 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.pos 128] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 5) (3 : Fin 5)

theorem input_n5_c66 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.pos 129] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 5) (4 : Fin 5)

theorem input_n5_c67 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.pos 133] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 5) (3 : Fin 5)

theorem input_n5_c68 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.pos 134] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 5) (4 : Fin 5)

theorem input_n5_c69 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.pos 136] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 5) (1 : Fin 5)

theorem input_n5_c70 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 64, Sat.Literal.pos 139] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 5) (4 : Fin 5)

theorem input_n5_c71 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 65, Sat.Literal.pos 140] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c72 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.pos 142] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 5) (2 : Fin 5)

theorem input_n5_c73 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 69, Sat.Literal.pos 144] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c74 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 70, Sat.Literal.pos 145] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 5) (0 : Fin 5)

theorem input_n5_c75 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 71, Sat.Literal.pos 146] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c76 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 72, Sat.Literal.pos 147] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c77 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 73, Sat.Literal.pos 148] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 5) (3 : Fin 5)

theorem input_n5_c78 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 128, Sat.Literal.neg 144, Sat.Literal.pos 129] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 5) (3 : Fin 5) (4 : Fin 5)

theorem input_n5_c79 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 133, Sat.Literal.neg 140, Sat.Literal.pos 130] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 5) (3 : Fin 5) (0 : Fin 5)

theorem input_n5_c80 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 134, Sat.Literal.neg 145, Sat.Literal.pos 130] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 5) (4 : Fin 5) (0 : Fin 5)

theorem input_n5_c81 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 139, Sat.Literal.neg 146, Sat.Literal.pos 136] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 5) (4 : Fin 5) (1 : Fin 5)

theorem input_n5_c82 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 144, Sat.Literal.neg 147, Sat.Literal.pos 142] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 5) (4 : Fin 5) (2 : Fin 5)

theorem input_n5_c83 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 145, Sat.Literal.neg 128, Sat.Literal.pos 148] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 5) (0 : Fin 5) (3 : Fin 5)

theorem input_n5_c84 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 79] :=
  h.toModel.predecessor_clause (0 : Fin 3) (4 : Fin 5)

theorem input_n5_c85 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 104] :=
  h.toModel.predecessor_clause (1 : Fin 3) (4 : Fin 5)

theorem input_n5_c86 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 129] :=
  h.toModel.predecessor_clause (2 : Fin 3) (4 : Fin 5)

theorem input_n5_c87 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 1, Sat.Literal.pos 26, Sat.Literal.pos 51] :=
  h.toModel.cycle_options_clause (0 : Fin 5)

theorem input_n5_c88 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 105] :=
  h.toModel.predecessor_clause (1 : Fin 3) (0 : Fin 5)

theorem input_n5_c89 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 130] :=
  h.toModel.predecessor_clause (2 : Fin 3) (0 : Fin 5)

theorem input_n5_c90 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 7, Sat.Literal.pos 32, Sat.Literal.pos 57] :=
  h.toModel.cycle_options_clause (1 : Fin 5)

theorem input_n5_c91 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 86] :=
  h.toModel.predecessor_clause (0 : Fin 3) (1 : Fin 5)

theorem input_n5_c92 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 111] :=
  h.toModel.predecessor_clause (1 : Fin 3) (1 : Fin 5)

theorem input_n5_c93 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 136] :=
  h.toModel.predecessor_clause (2 : Fin 3) (1 : Fin 5)

theorem input_n5_c94 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 13, Sat.Literal.pos 38, Sat.Literal.pos 63] :=
  h.toModel.cycle_options_clause (2 : Fin 5)

theorem input_n5_c95 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 92] :=
  h.toModel.predecessor_clause (0 : Fin 3) (2 : Fin 5)

theorem input_n5_c96 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117] :=
  h.toModel.predecessor_clause (1 : Fin 3) (2 : Fin 5)

theorem input_n5_c97 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 142] :=
  h.toModel.predecessor_clause (2 : Fin 3) (2 : Fin 5)

theorem input_n5_c98 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.pos 19, Sat.Literal.pos 44, Sat.Literal.pos 69] :=
  h.toModel.cycle_options_clause (3 : Fin 5)

theorem input_n5_c99 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 98] :=
  h.toModel.predecessor_clause (0 : Fin 3) (3 : Fin 5)

theorem input_n5_c100 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123] :=
  h.toModel.predecessor_clause (1 : Fin 3) (3 : Fin 5)

theorem input_n5_c101 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148] :=
  h.toModel.predecessor_clause (2 : Fin 3) (3 : Fin 5)

theorem input_n5_c102 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 33, Sat.Literal.neg 65] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 5) (1 : Fin 5) (3 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c103 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 58, Sat.Literal.neg 40] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 5) (1 : Fin 5) (3 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c104 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 34, Sat.Literal.neg 70] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 5) (1 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c105 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 59, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 5) (1 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c106 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 44, Sat.Literal.neg 70] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c107 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 69, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c108 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.neg 38, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c109 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 32, Sat.Literal.neg 13, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c110 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.neg 39, Sat.Literal.neg 71] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 5) (2 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c111 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 7, Sat.Literal.neg 64, Sat.Literal.neg 46] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 5) (2 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c112 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 44, Sat.Literal.neg 71] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c113 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 69, Sat.Literal.neg 21] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c114 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 13, Sat.Literal.neg 44, Sat.Literal.neg 72] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c115 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.neg 19, Sat.Literal.neg 72] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c116 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.neg 69, Sat.Literal.neg 22] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n5_c117 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 1, Sat.Literal.pos 150] :=
  h.first_advance_clause 0 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c118 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 51] :=
  h.first_conflict_clause 0 (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c119 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150, Sat.Literal.neg 7, Sat.Literal.neg 7, Sat.Literal.pos 151] :=
  h.advance_clause 0 (0 : Fin 4) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c120 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150, Sat.Literal.neg 57, Sat.Literal.neg 57] :=
  h.conflict_clause 0 (0 : Fin 4) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c121 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 151, Sat.Literal.neg 13, Sat.Literal.neg 13, Sat.Literal.pos 152] :=
  h.advance_clause 0 (1 : Fin 4) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c122 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 151, Sat.Literal.neg 63, Sat.Literal.neg 63] :=
  h.conflict_clause 0 (1 : Fin 4) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c123 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 152, Sat.Literal.neg 69, Sat.Literal.neg 69] :=
  h.conflict_clause 0 (2 : Fin 4) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c124 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 26] :=
  h.first_conflict_clause 1 (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c125 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 32, Sat.Literal.pos 178] :=
  h.first_advance_clause 7 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c126 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 178, Sat.Literal.neg 32, Sat.Literal.neg 38] :=
  h.conflict_clause 7 (0 : Fin 4) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c127 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 13, Sat.Literal.pos 194] :=
  h.first_advance_clause 11 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c128 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 194, Sat.Literal.neg 32, Sat.Literal.neg 19] :=
  h.conflict_clause 11 (0 : Fin 4) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c129 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 38, Sat.Literal.pos 202] :=
  h.first_advance_clause 13 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c130 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 202, Sat.Literal.neg 7, Sat.Literal.neg 44, Sat.Literal.pos 203] :=
  h.advance_clause 13 (0 : Fin 4) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n5_c131 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 203, Sat.Literal.neg 38, Sat.Literal.neg 45] :=
  h.conflict_clause 13 (1 : Fin 4) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c132 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 19, Sat.Literal.pos 218] :=
  h.first_advance_clause 17 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c133 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 218, Sat.Literal.neg 32, Sat.Literal.neg 45, Sat.Literal.pos 219] :=
  h.advance_clause 17 (0 : Fin 4) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n5_c134 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 219, Sat.Literal.neg 63, Sat.Literal.neg 1] :=
  h.conflict_clause 17 (1 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c135 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 19, Sat.Literal.pos 222] :=
  h.first_advance_clause 18 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c136 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 222, Sat.Literal.neg 32, Sat.Literal.neg 70, Sat.Literal.pos 223] :=
  h.advance_clause 18 (0 : Fin 4) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n5_c137 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 223, Sat.Literal.neg 63, Sat.Literal.neg 1] :=
  h.conflict_clause 18 (1 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c138 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 44, Sat.Literal.pos 226] :=
  h.first_advance_clause 19 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c139 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 226, Sat.Literal.neg 32, Sat.Literal.neg 45] :=
  h.conflict_clause 19 (0 : Fin 4) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c140 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 69, Sat.Literal.pos 230] :=
  h.first_advance_clause 20 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c141 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 7, Sat.Literal.neg 70, Sat.Literal.pos 231] :=
  h.advance_clause 20 (0 : Fin 4) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n5_c142 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 32, Sat.Literal.neg 70] :=
  h.conflict_clause 20 (0 : Fin 4) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n5_c143 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 231, Sat.Literal.neg 38, Sat.Literal.neg 1, Sat.Literal.pos 232] :=
  h.advance_clause 20 (1 : Fin 4) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c144 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 232, Sat.Literal.neg 69, Sat.Literal.neg 7] :=
  h.conflict_clause 20 (2 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c145 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 44, Sat.Literal.pos 234] :=
  h.first_advance_clause 21 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c146 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 234, Sat.Literal.neg 32, Sat.Literal.neg 70, Sat.Literal.pos 235] :=
  h.advance_clause 21 (0 : Fin 4) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n5_c147 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 235, Sat.Literal.neg 63, Sat.Literal.neg 1, Sat.Literal.pos 236] :=
  h.advance_clause 21 (1 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c148 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 236, Sat.Literal.neg 44, Sat.Literal.neg 32] :=
  h.conflict_clause 21 (2 : Fin 4) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c149 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 20, Sat.Literal.pos 242] :=
  h.first_advance_clause 23 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c150 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 242, Sat.Literal.neg 7, Sat.Literal.neg 1, Sat.Literal.pos 243] :=
  h.advance_clause 23 (0 : Fin 4) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c151 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 242, Sat.Literal.neg 32, Sat.Literal.neg 1] :=
  h.conflict_clause 23 (0 : Fin 4) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c152 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 243, Sat.Literal.neg 38, Sat.Literal.neg 7] :=
  h.conflict_clause 23 (1 : Fin 4) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c153 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 45, Sat.Literal.pos 250] :=
  h.first_advance_clause 25 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c154 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 250, Sat.Literal.neg 32, Sat.Literal.neg 1, Sat.Literal.pos 251] :=
  h.advance_clause 25 (0 : Fin 4) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n5_c155 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 251, Sat.Literal.neg 13, Sat.Literal.neg 32, Sat.Literal.pos 252] :=
  h.advance_clause 25 (1 : Fin 4) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n5_c156 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 251, Sat.Literal.neg 63, Sat.Literal.neg 7] :=
  h.conflict_clause 25 (1 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n5_c157 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 251, Sat.Literal.neg 63, Sat.Literal.neg 32] :=
  h.conflict_clause 25 (1 : Fin 4) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n5_c158 (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) :
    val.satisfies [Sat.Literal.neg 252, Sat.Literal.neg 69, Sat.Literal.neg 13] :=
  h.conflict_clause 25 (2 : Fin 4) (2 : Fin 3) (0 : Fin 3) (by decide)

lrat_proof cert_n5_root
  "p cnf 266 159\n4 16 29 41 54 66 0\n5 21 30 46 55 71 0\n8 12 33 37 58 62 0\n9 17 34 42 59 67 0\n10 22 35 47 60 72 0\n14 18 39 43 64 68 0\n15 23 40 48 65 73 0\n20 24 45 49 70 74 0\n-2 77 0\n-5 80 0\n-8 83 0\n-9 84 0\n-10 85 0\n-12 87 0\n-14 89 0\n-15 90 0\n-16 91 0\n-17 92 0\n-18 93 0\n-20 95 0\n-21 96 0\n-22 97 0\n-23 98 0\n-24 99 0\n-77 -83 78 0\n-77 -85 80 0\n-83 -89 84 0\n-83 -90 85 0\n-84 -95 85 0\n-86 -77 87 0\n-89 -91 86 0\n-89 -92 87 0\n-91 -78 93 0\n-92 -83 93 0\n-95 -98 93 0\n-96 -77 97 0\n-97 -83 98 0\n-97 -84 99 0\n-98 -89 99 0\n-29 104 0\n-30 105 0\n-33 108 0\n-34 109 0\n-35 110 0\n-37 112 0\n-39 114 0\n-40 115 0\n-41 116 0\n-42 117 0\n-43 118 0\n-45 120 0\n-46 121 0\n-47 122 0\n-48 123 0\n-49 124 0\n-104 -120 105 0\n-109 -116 106 0\n-110 -121 106 0\n-114 -117 112 0\n-115 -122 112 0\n-117 -108 118 0\n-120 -122 117 0\n-120 -123 118 0\n-121 -104 124 0\n-123 -114 124 0\n-54 129 0\n-55 130 0\n-59 134 0\n-60 135 0\n-62 137 0\n-65 140 0\n-66 141 0\n-68 143 0\n-70 145 0\n-71 146 0\n-72 147 0\n-73 148 0\n-74 149 0\n-129 -145 130 0\n-134 -141 131 0\n-135 -146 131 0\n-140 -147 137 0\n-145 -148 143 0\n-146 -129 149 0\n-80 0\n-105 0\n-130 0\n2 27 52 0\n-106 0\n-131 0\n8 33 58 0\n-87 0\n-112 0\n-137 0\n14 39 64 0\n-93 0\n-118 0\n-143 0\n20 45 70 0\n-99 0\n-124 0\n-149 0\n-2 -34 -66 0\n-2 -59 -41 0\n-2 -35 -71 0\n-2 -60 -46 0\n-4 -45 -71 0\n-4 -70 -46 0\n-8 -39 -67 0\n-33 -14 -67 0\n-8 -40 -72 0\n-8 -65 -47 0\n-9 -45 -72 0\n-34 -70 -22 0\n-14 -45 -73 0\n-39 -20 -73 0\n-39 -70 -23 0\n-2 -2 151 0\n-52 -52 0\n-151 -8 -8 152 0\n-151 -58 -58 0\n-152 -14 -14 153 0\n-152 -64 -64 0\n-153 -70 -70 0\n-27 -27 0\n-2 -33 179 0\n-179 -33 -39 0\n-2 -14 195 0\n-195 -33 -20 0\n-2 -39 203 0\n-203 -8 -45 204 0\n-204 -39 -46 0\n-2 -20 219 0\n-219 -33 -46 220 0\n-220 -64 -2 0\n-2 -20 223 0\n-223 -33 -71 224 0\n-224 -64 -2 0\n-2 -45 227 0\n-227 -33 -46 0\n-2 -70 231 0\n-231 -8 -71 232 0\n-231 -33 -71 0\n-232 -39 -2 233 0\n-233 -70 -8 0\n-2 -45 235 0\n-235 -33 -71 236 0\n-236 -64 -2 237 0\n-237 -45 -33 0\n-2 -21 243 0\n-243 -8 -2 244 0\n-243 -33 -2 0\n-244 -39 -8 0\n-2 -46 251 0\n-251 -33 -2 252 0\n-252 -14 -33 253 0\n-252 -64 -8 0\n-252 -64 -33 0\n-253 -70 -14 0\n"
  "160 -5 0 85 10 0\n161 -30 0 86 41 0\n162 -55 0 87 67 0\n163 -12 0 92 14 0\n164 -37 0 93 45 0\n165 -62 0 94 70 0\n166 -18 0 96 19 0\n167 -43 0 97 50 0\n168 -68 0 98 73 0\n169 -24 0 100 24 0\n170 -49 0 101 55 0\n171 -74 0 102 78 0\n172 -2 151 0 118 0\n173 -52 0 119 0\n174 -151 -8 152 0 120 0\n175 -151 -58 0 121 0\n176 -152 -14 153 0 122 0\n177 -152 -64 0 123 0\n178 -153 -70 0 124 0\n179 -27 0 125 0\n180 2 0 179 173 88 0\n181 77 0 180 9 0\n182 151 0 180 172 0\n183 -85 0 181 85 26 0\n184 -86 0 181 92 30 0\n185 -58 0 182 175 0\n186 -10 0 183 13 0\n187 -33 179 0 180 126 0\n188 -14 195 0 180 128 0\n189 -39 203 0 180 130 0\n190 -20 219 0 180 133 0\n191 -220 -64 0 180 135 0\n192 -20 223 0 180 136 0\n193 -224 -64 0 180 138 0\n194 -45 227 0 180 139 0\n195 -70 231 0 180 141 0\n196 -232 -39 233 0 180 144 0\n197 -45 235 0 180 146 0\n198 -236 -64 237 0 180 148 0\n199 -21 243 0 180 150 0\n200 -243 -8 244 0 180 151 0\n201 -243 -33 0 180 152 0\n202 -46 251 0 180 154 0\n203 -251 -33 252 0 180 155 0\n204 -64 -252 0 163 164 185 165 157 158 3 0\n205 -40 35 60 22 -8 0 93 186 47 111 60 5 53 0\n206 -8 35 -20 60 0 96 182 183 168 167 166 101 94 186 20 35 23 29 11 174 28 27 37 177 16 15 22 6 205 46 116 65 54 7 71 112 82 5 76 0\n207 -21 0 181 100 185 182 21 199 36 201 38 91 11 174 200 27 177 153 15 95 0\n208 -14 -8 35 -45 60 0 97 183 100 94 186 11 28 16 51 63 54 15 115 39 23 37 22 205 7 71 112 82 5 76 0\n209 -46 -20 0 180 89 165 185 164 163 190 52 106 58 44 206 3 187 134 129 127 191 188 95 0\n210 -20 0 207 162 161 160 180 90 165 185 164 163 192 209 2 75 105 81 69 206 3 187 129 137 127 188 193 95 0\n211 22 -39 -8 -46 0 180 89 183 101 210 98 94 186 189 132 131 99 74 83 77 117 46 65 54 11 28 16 52 58 44 106 205 7 71 112 82 5 76 0\n212 -39 -8 -46 0 101 181 96 93 210 87 100 180 90 11 25 33 17 34 18 52 64 40 46 189 109 132 59 131 49 99 74 108 79 66 211 22 114 38 12 4 68 104 80 1 72 0\n213 -8 -46 0 180 89 182 210 52 58 44 106 174 177 212 95 176 208 178 99 0\n214 -46 0 165 185 164 163 210 202 213 3 187 140 203 127 194 204 95 99 156 159 0\n215 71 0 214 160 161 162 207 2 0\n216 146 0 215 75 0\n217 -35 0 215 180 105 0\n218 -135 0 216 90 81 0\n219 -129 0 216 102 84 0\n220 -60 0 218 69 0\n221 -54 0 219 66 0\n222 -34 -33 0 86 215 169 170 210 171 184 180 89 221 187 127 143 195 8 149 197 147 198 95 15 31 17 51 56 40 107 43 103 57 1 48 0\n223 -59 -33 0 86 215 169 170 210 171 184 180 90 221 187 127 143 195 8 149 197 147 198 95 15 31 17 51 56 40 107 68 104 80 1 72 0\n224 -33 0 97 171 210 170 169 215 92 100 217 220 186 42 187 143 61 127 195 49 8 51 197 149 62 147 53 198 95 15 110 32 18 222 223 4 12 113 38 5 22 0\n225 8 0 224 185 91 0\n226 83 0 225 11 0\n227 152 0 225 182 174 0\n228 78 0 226 181 25 0\n229 -92 0 226 96 34 0\n230 -64 0 227 177 0\n231 -91 0 228 96 33 0\n232 -17 0 229 18 0\n233 -16 0 231 17 0\n234 -70 0 227 215 225 168 230 167 166 178 195 145 176 142 6 196 0\n235 45 0 234 169 170 210 171 8 0\n236 120 0 235 51 0\n237 -14 0 235 217 225 220 208 0\n238 -4 0 235 215 107 0\n239 -104 0 236 86 56 0\n240 39 0 237 166 167 230 168 6 0\n241 -29 0 239 40 0\n242 114 0 240 46 0\n243 -117 0 242 93 59 0\n244 -42 0 243 49 0\n245 -122 0 243 236 62 0\n246 -47 0 245 53 0\n247 -9 0 235 100 217 220 246 186 12 113 38 5 22 0\n248 -66 67 0 180 90 232 247 244 72 103 80 4 68 0\n249 67 0 241 221 238 233 180 89 232 247 244 248 1 48 104 57 4 43 0\n250 0 249 240 225 109 0\n"

theorem raw_n5_root (word : Fin 5 → Fin 3) :
    ClauseProof (fun val => ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val ∧ True) Sat.Clause.nil := by
  intro val hh
  have h := hh.left
  have bad := cert_n5_root (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 173) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 182) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 191) (val 192) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 201) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 210) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 219) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 228) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 237) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 246) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 255) (val 256) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 265)
  exact Or.elim (bad)
    (fun badL0 => Or.elim (badL0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c0 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2.1) (badL6.2.2.2.2.1) (badL6.2.2.2.2.2))
    (fun badR6 => input_n5_c1 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2.1) (badR6.2.2.2.2.1) (badR6.2.2.2.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c2 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2.1) (badL6.2.2.2.2.1) (badL6.2.2.2.2.2))
    (fun badR6 => input_n5_c3 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2.1) (badR6.2.2.2.2.1) (badR6.2.2.2.2.2))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c4 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2.1) (badL6.2.2.2.2.1) (badL6.2.2.2.2.2))
    (fun badR6 => input_n5_c5 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2.1) (badR6.2.2.2.2.1) (badR6.2.2.2.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c6 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2.1) (badL6.2.2.2.2.1) (badL6.2.2.2.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c7 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => input_n5_c8 word val h (badR7.1) (badR7.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c9 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c10 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c11 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c12 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c13 word val h (badR7.1) (badR7.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c14 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c15 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c16 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c17 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c18 word val h (badR7.1) (badR7.2)))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c19 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c20 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c21 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c22 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c23 word val h (badR7.1) (badR7.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c24 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c25 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c26 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c27 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c28 word val h (badR7.1) (badR7.2.1) (badR7.2.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c29 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c30 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c31 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c32 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c33 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c34 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c35 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c36 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c37 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c38 word val h (badR7.1) (badR7.2.1) (badR7.2.2))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c39 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c40 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c41 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c42 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c43 word val h (badR7.1) (badR7.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c44 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c45 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c46 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c47 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c48 word val h (badR7.1) (badR7.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c49 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c50 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c51 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c52 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c53 word val h (badR7.1) (badR7.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c54 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c55 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c56 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c57 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c58 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c59 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c60 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c61 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c62 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c63 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c64 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c65 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c66 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c67 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c68 word val h (badR7.1) (badR7.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c69 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c70 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c71 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c72 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c73 word val h (badR7.1) (badR7.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c74 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c75 word val h (badR6.1) (badR6.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c76 word val h (badL6.1) (badL6.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c77 word val h (badL7.1) (badL7.2))
    (fun badR7 => input_n5_c78 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))))))
    (fun badR0 => Or.elim (badR0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c79 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c80 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c81 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c82 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c83 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c84 word val h (badL6))
    (fun badR6 => input_n5_c85 word val h (badR6)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c86 word val h (badL6))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c87 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c88 word val h (badR7))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c89 word val h (badL6))
    (fun badR6 => input_n5_c90 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c91 word val h (badL6))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c92 word val h (badL7))
    (fun badR7 => input_n5_c93 word val h (badR7)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c94 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c95 word val h (badR6)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c96 word val h (badL6))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c97 word val h (badL7))
    (fun badR7 => input_n5_c98 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c99 word val h (badL6))
    (fun badR6 => input_n5_c100 word val h (badR6)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c101 word val h (badL6))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c102 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c103 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c104 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c105 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c106 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c107 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c108 word val h (badR7.1) (badR7.2.1) (badR7.2.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c109 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c110 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c111 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c112 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c113 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c114 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c115 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c116 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c117 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c118 word val h (badR7.1) (badR7.2))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c119 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => input_n5_c120 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c121 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c122 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c123 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c124 word val h (badL6.1) (badL6.2))
    (fun badR6 => input_n5_c125 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c126 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c127 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c128 word val h (badR7.1) (badR7.2.1) (badR7.2.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c129 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c130 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c131 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c132 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c133 word val h (badR7.1) (badR7.2.1) (badR7.2.2.1) (badR7.2.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c134 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c135 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c136 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c137 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c138 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c139 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c140 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c141 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c142 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c143 word val h (badR7.1) (badR7.2.1) (badR7.2.2.1) (badR7.2.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c144 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c145 word val h (badR6.1) (badR6.2.1) (badR6.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c146 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c147 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => input_n5_c148 word val h (badR7.1) (badR7.2.1) (badR7.2.2))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c149 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => input_n5_c150 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c151 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c152 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c153 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => input_n5_c154 word val h (badL6.1) (badL6.2.1) (badL6.2.2.1) (badL6.2.2.2))
    (fun badR6 => input_n5_c155 word val h (badR6.1) (badR6.2.1) (badR6.2.2.1) (badR6.2.2.2)))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => input_n5_c156 word val h (badL6.1) (badL6.2.1) (badL6.2.2))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n5_c157 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => input_n5_c158 word val h (badR7.1) (badR7.2.1) (badR7.2.2)))))))))

theorem exclude_n5_root (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) (_hp : True) : False :=
  raw_n5_root word val ⟨h, True.intro⟩

theorem universal_n5_root (word : Fin 5 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 5) lexPerm val) : False :=
  raw_n5_root word val ⟨h, True.intro⟩
end OPG1808SmallOrders


-- Bundled whole source: LeafN6Root.lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OPG1808SmallOrders
open ModuleOPG1808Certificate OrdinaryLRATBridge

theorem input_n6_c0 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 2, Sat.Literal.pos 12, Sat.Literal.pos 38, Sat.Literal.pos 48, Sat.Literal.pos 74, Sat.Literal.pos 84] :=
  h.toModel.orientation_clause (0 : Fin 6) (2 : Fin 6) (by decide)

theorem input_n6_c1 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 3, Sat.Literal.pos 18, Sat.Literal.pos 39, Sat.Literal.pos 54, Sat.Literal.pos 75, Sat.Literal.pos 90] :=
  h.toModel.orientation_clause (0 : Fin 6) (3 : Fin 6) (by decide)

theorem input_n6_c2 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 4, Sat.Literal.pos 24, Sat.Literal.pos 40, Sat.Literal.pos 60, Sat.Literal.pos 76, Sat.Literal.pos 96] :=
  h.toModel.orientation_clause (0 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c3 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 5, Sat.Literal.pos 30, Sat.Literal.pos 41, Sat.Literal.pos 66, Sat.Literal.pos 77, Sat.Literal.pos 102] :=
  h.toModel.orientation_clause (0 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c4 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 8, Sat.Literal.pos 13, Sat.Literal.pos 44, Sat.Literal.pos 49, Sat.Literal.pos 80, Sat.Literal.pos 85] :=
  h.toModel.orientation_clause (1 : Fin 6) (2 : Fin 6) (by decide)

theorem input_n6_c5 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 9, Sat.Literal.pos 19, Sat.Literal.pos 45, Sat.Literal.pos 55, Sat.Literal.pos 81, Sat.Literal.pos 91] :=
  h.toModel.orientation_clause (1 : Fin 6) (3 : Fin 6) (by decide)

theorem input_n6_c6 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 10, Sat.Literal.pos 25, Sat.Literal.pos 46, Sat.Literal.pos 61, Sat.Literal.pos 82, Sat.Literal.pos 97] :=
  h.toModel.orientation_clause (1 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c7 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.neg 97] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 6) (1 : Fin 6) (by decide)

theorem input_n6_c8 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 11, Sat.Literal.pos 31, Sat.Literal.pos 47, Sat.Literal.pos 67, Sat.Literal.pos 83, Sat.Literal.pos 103] :=
  h.toModel.orientation_clause (1 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c9 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 15, Sat.Literal.pos 20, Sat.Literal.pos 51, Sat.Literal.pos 56, Sat.Literal.pos 87, Sat.Literal.pos 92] :=
  h.toModel.orientation_clause (2 : Fin 6) (3 : Fin 6) (by decide)

theorem input_n6_c10 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 16, Sat.Literal.pos 26, Sat.Literal.pos 52, Sat.Literal.pos 62, Sat.Literal.pos 88, Sat.Literal.pos 98] :=
  h.toModel.orientation_clause (2 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c11 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 17, Sat.Literal.pos 32, Sat.Literal.pos 53, Sat.Literal.pos 68, Sat.Literal.pos 89, Sat.Literal.pos 104] :=
  h.toModel.orientation_clause (2 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c12 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 22, Sat.Literal.pos 27, Sat.Literal.pos 58, Sat.Literal.pos 63, Sat.Literal.pos 94, Sat.Literal.pos 99] :=
  h.toModel.orientation_clause (3 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c13 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.neg 58] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c14 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.neg 94] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (by decide)

theorem input_n6_c15 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 23, Sat.Literal.pos 33, Sat.Literal.pos 59, Sat.Literal.pos 69, Sat.Literal.pos 95, Sat.Literal.pos 105] :=
  h.toModel.orientation_clause (3 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c16 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 23, Sat.Literal.neg 59] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (3 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c17 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 29, Sat.Literal.pos 34, Sat.Literal.pos 65, Sat.Literal.pos 70, Sat.Literal.pos 101, Sat.Literal.pos 106] :=
  h.toModel.orientation_clause (4 : Fin 6) (5 : Fin 6) (by decide)

theorem input_n6_c18 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.pos 109] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 6) (1 : Fin 6)

theorem input_n6_c19 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.pos 110] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c20 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.pos 111] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c21 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.pos 112] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 6) (4 : Fin 6)

theorem input_n6_c22 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.pos 113] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 6) (5 : Fin 6)

theorem input_n6_c23 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.pos 116] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c24 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.pos 117] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c25 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.pos 118] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c26 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.pos 119] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 6) (5 : Fin 6)

theorem input_n6_c27 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.pos 120] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 6) (0 : Fin 6)

theorem input_n6_c28 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 13, Sat.Literal.pos 121] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 6) (1 : Fin 6)

theorem input_n6_c29 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.pos 123] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c30 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 16, Sat.Literal.pos 124] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c31 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.pos 125] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c32 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.pos 126] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c33 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.pos 127] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c34 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 20, Sat.Literal.pos 128] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 6) (2 : Fin 6)

theorem input_n6_c35 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.pos 130] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c36 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 23, Sat.Literal.pos 131] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c37 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 24, Sat.Literal.pos 132] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c38 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.pos 133] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c39 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.pos 134] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c40 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 27, Sat.Literal.pos 135] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 6) (3 : Fin 6)

theorem input_n6_c41 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.pos 137] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c42 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 30, Sat.Literal.pos 138] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c43 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 31, Sat.Literal.pos 139] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c44 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 32, Sat.Literal.pos 140] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c45 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.pos 141] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c46 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34, Sat.Literal.pos 142] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 6) (4 : Fin 6)

theorem input_n6_c47 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 116, Sat.Literal.pos 110] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c48 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 117, Sat.Literal.pos 111] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c49 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 119, Sat.Literal.pos 113] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (1 : Fin 6) (5 : Fin 6)

theorem input_n6_c50 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 110, Sat.Literal.neg 125, Sat.Literal.pos 113] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c51 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 111, Sat.Literal.neg 131, Sat.Literal.pos 113] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c52 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 112, Sat.Literal.neg 137, Sat.Literal.pos 113] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c53 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 123, Sat.Literal.pos 117] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c54 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 124, Sat.Literal.pos 118] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c55 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 125, Sat.Literal.pos 119] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c56 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 130, Sat.Literal.pos 118] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c57 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 131, Sat.Literal.pos 119] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c58 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 118, Sat.Literal.neg 137, Sat.Literal.pos 119] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c59 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 120, Sat.Literal.neg 109, Sat.Literal.pos 121] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (0 : Fin 6) (1 : Fin 6)

theorem input_n6_c60 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 126, Sat.Literal.pos 120] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c61 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 127, Sat.Literal.pos 121] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c62 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 130, Sat.Literal.pos 124] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c63 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 131, Sat.Literal.pos 125] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c64 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 132, Sat.Literal.pos 120] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c65 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 133, Sat.Literal.pos 121] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c66 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 137, Sat.Literal.pos 125] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c67 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 125, Sat.Literal.neg 139, Sat.Literal.pos 121] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c68 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 126, Sat.Literal.neg 110, Sat.Literal.pos 128] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c69 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 127, Sat.Literal.neg 116, Sat.Literal.pos 128] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c70 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 130, Sat.Literal.neg 132, Sat.Literal.pos 126] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c71 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 130, Sat.Literal.neg 133, Sat.Literal.pos 127] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c72 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 130, Sat.Literal.neg 134, Sat.Literal.pos 128] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c73 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 130, Sat.Literal.neg 137, Sat.Literal.pos 131] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c74 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 131, Sat.Literal.neg 139, Sat.Literal.pos 127] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c75 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 131, Sat.Literal.neg 140, Sat.Literal.pos 128] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c76 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 132, Sat.Literal.neg 109, Sat.Literal.pos 133] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (0 : Fin 6) (1 : Fin 6)

theorem input_n6_c77 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 132, Sat.Literal.neg 110, Sat.Literal.pos 134] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c78 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 132, Sat.Literal.neg 111, Sat.Literal.pos 135] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c79 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 133, Sat.Literal.neg 116, Sat.Literal.pos 134] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c80 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 133, Sat.Literal.neg 117, Sat.Literal.pos 135] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c81 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 134, Sat.Literal.neg 123, Sat.Literal.pos 135] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c82 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 137, Sat.Literal.neg 139, Sat.Literal.pos 133] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c83 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 137, Sat.Literal.neg 140, Sat.Literal.pos 134] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c84 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 137, Sat.Literal.neg 141, Sat.Literal.pos 135] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 6) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c85 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 138, Sat.Literal.neg 109, Sat.Literal.pos 139] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (0 : Fin 6) (1 : Fin 6)

theorem input_n6_c86 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 139, Sat.Literal.neg 116, Sat.Literal.pos 140] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c87 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 139, Sat.Literal.neg 117, Sat.Literal.pos 141] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c88 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 139, Sat.Literal.neg 118, Sat.Literal.pos 142] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c89 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 140, Sat.Literal.neg 123, Sat.Literal.pos 141] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c90 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 140, Sat.Literal.neg 124, Sat.Literal.pos 142] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c91 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 141, Sat.Literal.neg 130, Sat.Literal.pos 142] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c92 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.pos 146] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c93 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.pos 147] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c94 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 40, Sat.Literal.pos 148] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 6) (4 : Fin 6)

theorem input_n6_c95 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 41, Sat.Literal.pos 149] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 6) (5 : Fin 6)

theorem input_n6_c96 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.pos 152] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c97 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.pos 153] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c98 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.pos 154] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c99 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 47, Sat.Literal.pos 155] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 6) (5 : Fin 6)

theorem input_n6_c100 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 48, Sat.Literal.pos 156] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 6) (0 : Fin 6)

theorem input_n6_c101 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 49, Sat.Literal.pos 157] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 6) (1 : Fin 6)

theorem input_n6_c102 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.pos 159] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c103 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.pos 160] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c104 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.pos 161] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c105 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.pos 162] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c106 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 55, Sat.Literal.pos 163] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c107 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 56, Sat.Literal.pos 164] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 6) (2 : Fin 6)

theorem input_n6_c108 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.pos 166] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c109 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.pos 167] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c110 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.pos 168] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c111 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.pos 169] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c112 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 62, Sat.Literal.pos 170] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c113 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 63, Sat.Literal.pos 171] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 6) (3 : Fin 6)

theorem input_n6_c114 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 65, Sat.Literal.pos 173] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c115 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.pos 174] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c116 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.pos 175] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c117 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.pos 176] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c118 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 69, Sat.Literal.pos 177] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c119 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 70, Sat.Literal.pos 178] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 6) (4 : Fin 6)

theorem input_n6_c120 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 146, Sat.Literal.neg 160, Sat.Literal.pos 148] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c121 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 146, Sat.Literal.neg 161, Sat.Literal.pos 149] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 6) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c122 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 147, Sat.Literal.neg 166, Sat.Literal.pos 148] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c123 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 147, Sat.Literal.neg 167, Sat.Literal.pos 149] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c124 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148, Sat.Literal.neg 173, Sat.Literal.pos 149] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c125 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 152, Sat.Literal.neg 156, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (2 : Fin 6) (0 : Fin 6)

theorem input_n6_c126 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 153, Sat.Literal.neg 162, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c127 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 153, Sat.Literal.neg 167, Sat.Literal.pos 155] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c128 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 154, Sat.Literal.neg 168, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c129 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 154, Sat.Literal.neg 173, Sat.Literal.pos 155] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c130 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 155, Sat.Literal.neg 174, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 6) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c131 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 159, Sat.Literal.neg 163, Sat.Literal.pos 157] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 6) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c132 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 160, Sat.Literal.neg 168, Sat.Literal.pos 156] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c133 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 160, Sat.Literal.neg 169, Sat.Literal.pos 157] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 6) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c134 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 160, Sat.Literal.neg 173, Sat.Literal.pos 161] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c135 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 161, Sat.Literal.neg 175, Sat.Literal.pos 157] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c136 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 163, Sat.Literal.neg 152, Sat.Literal.pos 164] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c137 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 168, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c138 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 169, Sat.Literal.pos 163] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c139 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 170, Sat.Literal.pos 164] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c140 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 167, Sat.Literal.neg 175, Sat.Literal.pos 163] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c141 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 167, Sat.Literal.neg 176, Sat.Literal.pos 164] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c142 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 168, Sat.Literal.neg 147, Sat.Literal.pos 171] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c143 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 169, Sat.Literal.neg 152, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c144 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 169, Sat.Literal.neg 153, Sat.Literal.pos 171] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c145 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 170, Sat.Literal.neg 159, Sat.Literal.pos 171] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c146 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 174, Sat.Literal.pos 168] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c147 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 175, Sat.Literal.pos 169] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c148 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 176, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c149 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 177, Sat.Literal.pos 171] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 6) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c150 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 174, Sat.Literal.neg 147, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c151 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 174, Sat.Literal.neg 148, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (0 : Fin 6) (4 : Fin 6)

theorem input_n6_c152 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 152, Sat.Literal.pos 176] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (1 : Fin 6) (2 : Fin 6)

theorem input_n6_c153 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 153, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c154 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 154, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c155 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 176, Sat.Literal.neg 159, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c156 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 176, Sat.Literal.neg 160, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c157 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 177, Sat.Literal.neg 166, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c158 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.pos 182] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c159 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.pos 183] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c160 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.pos 184] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 6) (4 : Fin 6)

theorem input_n6_c161 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 77, Sat.Literal.pos 185] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 6) (5 : Fin 6)

theorem input_n6_c162 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 81, Sat.Literal.pos 189] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c163 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.pos 190] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c164 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.pos 191] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 6) (5 : Fin 6)

theorem input_n6_c165 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 85, Sat.Literal.pos 193] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 6) (1 : Fin 6)

theorem input_n6_c166 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 87, Sat.Literal.pos 195] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c167 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.pos 196] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c168 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 89, Sat.Literal.pos 197] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 6) (5 : Fin 6)

theorem input_n6_c169 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 90, Sat.Literal.pos 198] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c170 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 91, Sat.Literal.pos 199] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c171 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 92, Sat.Literal.pos 200] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 6) (2 : Fin 6)

theorem input_n6_c172 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.pos 202] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c173 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 95, Sat.Literal.pos 203] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c174 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.pos 204] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c175 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 97, Sat.Literal.pos 205] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c176 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 98, Sat.Literal.pos 206] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c177 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 99, Sat.Literal.pos 207] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 6) (3 : Fin 6)

theorem input_n6_c178 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.pos 209] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c179 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 102, Sat.Literal.pos 210] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c180 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 103, Sat.Literal.pos 211] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c181 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 104, Sat.Literal.pos 212] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c182 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 105, Sat.Literal.pos 213] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c183 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 106, Sat.Literal.pos 214] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 6) (4 : Fin 6)

theorem input_n6_c184 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 182, Sat.Literal.neg 196, Sat.Literal.pos 184] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c185 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 183, Sat.Literal.neg 202, Sat.Literal.pos 184] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c186 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 183, Sat.Literal.neg 203, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c187 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 184, Sat.Literal.neg 209, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c188 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 189, Sat.Literal.neg 198, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (0 : Fin 6)

theorem input_n6_c189 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 189, Sat.Literal.neg 202, Sat.Literal.pos 190] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c190 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 189, Sat.Literal.neg 203, Sat.Literal.pos 191] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6)

theorem input_n6_c191 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 204, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c192 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 209, Sat.Literal.pos 191] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c193 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 191, Sat.Literal.neg 210, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 6) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c194 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 195, Sat.Literal.neg 199, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 6) (3 : Fin 6) (1 : Fin 6)

theorem input_n6_c195 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 196, Sat.Literal.neg 205, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 6) (4 : Fin 6) (1 : Fin 6)

theorem input_n6_c196 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 196, Sat.Literal.neg 209, Sat.Literal.pos 197] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c197 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 197, Sat.Literal.neg 211, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c198 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 198, Sat.Literal.neg 182, Sat.Literal.pos 200] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c199 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 202, Sat.Literal.neg 204, Sat.Literal.pos 198] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (0 : Fin 6)

theorem input_n6_c200 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 202, Sat.Literal.neg 206, Sat.Literal.pos 200] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (2 : Fin 6)

theorem input_n6_c201 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 202, Sat.Literal.neg 209, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

theorem input_n6_c202 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 203, Sat.Literal.neg 210, Sat.Literal.pos 198] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c203 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 203, Sat.Literal.neg 211, Sat.Literal.pos 199] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c204 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 203, Sat.Literal.neg 212, Sat.Literal.pos 200] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c205 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 204, Sat.Literal.neg 182, Sat.Literal.pos 206] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c206 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 204, Sat.Literal.neg 183, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c207 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 205, Sat.Literal.neg 189, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c208 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 206, Sat.Literal.neg 195, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (2 : Fin 6) (3 : Fin 6)

theorem input_n6_c209 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 209, Sat.Literal.neg 210, Sat.Literal.pos 204] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (5 : Fin 6) (0 : Fin 6)

theorem input_n6_c210 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 209, Sat.Literal.neg 211, Sat.Literal.pos 205] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (5 : Fin 6) (1 : Fin 6)

theorem input_n6_c211 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 209, Sat.Literal.neg 212, Sat.Literal.pos 206] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (5 : Fin 6) (2 : Fin 6)

theorem input_n6_c212 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 209, Sat.Literal.neg 213, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 6) (5 : Fin 6) (3 : Fin 6)

theorem input_n6_c213 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 210, Sat.Literal.neg 182, Sat.Literal.pos 212] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (0 : Fin 6) (2 : Fin 6)

theorem input_n6_c214 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 210, Sat.Literal.neg 183, Sat.Literal.pos 213] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (0 : Fin 6) (3 : Fin 6)

theorem input_n6_c215 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 210, Sat.Literal.neg 184, Sat.Literal.pos 214] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (0 : Fin 6) (4 : Fin 6)

theorem input_n6_c216 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 211, Sat.Literal.neg 189, Sat.Literal.pos 213] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (1 : Fin 6) (3 : Fin 6)

theorem input_n6_c217 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 211, Sat.Literal.neg 190, Sat.Literal.pos 214] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (1 : Fin 6) (4 : Fin 6)

theorem input_n6_c218 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 212, Sat.Literal.neg 196, Sat.Literal.pos 214] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (2 : Fin 6) (4 : Fin 6)

theorem input_n6_c219 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 213, Sat.Literal.neg 202, Sat.Literal.pos 214] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 6) (3 : Fin 6) (4 : Fin 6)

theorem input_n6_c220 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 113] :=
  h.toModel.predecessor_clause (0 : Fin 3) (5 : Fin 6)

theorem input_n6_c221 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 149] :=
  h.toModel.predecessor_clause (1 : Fin 3) (5 : Fin 6)

theorem input_n6_c222 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 185] :=
  h.toModel.predecessor_clause (2 : Fin 3) (5 : Fin 6)

theorem input_n6_c223 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 1, Sat.Literal.pos 37, Sat.Literal.pos 73] :=
  h.toModel.cycle_options_clause (0 : Fin 6)

theorem input_n6_c224 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150] :=
  h.toModel.predecessor_clause (1 : Fin 3) (0 : Fin 6)

theorem input_n6_c225 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 186] :=
  h.toModel.predecessor_clause (2 : Fin 3) (0 : Fin 6)

theorem input_n6_c226 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 8, Sat.Literal.pos 44, Sat.Literal.pos 80] :=
  h.toModel.cycle_options_clause (1 : Fin 6)

theorem input_n6_c227 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 121] :=
  h.toModel.predecessor_clause (0 : Fin 3) (1 : Fin 6)

theorem input_n6_c228 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 157] :=
  h.toModel.predecessor_clause (1 : Fin 3) (1 : Fin 6)

theorem input_n6_c229 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 193] :=
  h.toModel.predecessor_clause (2 : Fin 3) (1 : Fin 6)

theorem input_n6_c230 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 15, Sat.Literal.pos 51, Sat.Literal.pos 87] :=
  h.toModel.cycle_options_clause (2 : Fin 6)

theorem input_n6_c231 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 128] :=
  h.toModel.predecessor_clause (0 : Fin 3) (2 : Fin 6)

theorem input_n6_c232 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164] :=
  h.toModel.predecessor_clause (1 : Fin 3) (2 : Fin 6)

theorem input_n6_c233 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 200] :=
  h.toModel.predecessor_clause (2 : Fin 3) (2 : Fin 6)

theorem input_n6_c234 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 22, Sat.Literal.pos 58, Sat.Literal.pos 94] :=
  h.toModel.cycle_options_clause (3 : Fin 6)

theorem input_n6_c235 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 135] :=
  h.toModel.predecessor_clause (0 : Fin 3) (3 : Fin 6)

theorem input_n6_c236 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 171] :=
  h.toModel.predecessor_clause (1 : Fin 3) (3 : Fin 6)

theorem input_n6_c237 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 207] :=
  h.toModel.predecessor_clause (2 : Fin 3) (3 : Fin 6)

theorem input_n6_c238 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.pos 29, Sat.Literal.pos 65, Sat.Literal.pos 101] :=
  h.toModel.cycle_options_clause (4 : Fin 6)

theorem input_n6_c239 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 142] :=
  h.toModel.predecessor_clause (0 : Fin 3) (4 : Fin 6)

theorem input_n6_c240 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 178] :=
  h.toModel.predecessor_clause (1 : Fin 3) (4 : Fin 6)

theorem input_n6_c241 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 214] :=
  h.toModel.predecessor_clause (2 : Fin 3) (4 : Fin 6)

theorem input_n6_c242 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 44, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c243 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 45, Sat.Literal.neg 90] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (1 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c244 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 81, Sat.Literal.neg 54] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (1 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c245 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 46, Sat.Literal.neg 96] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (1 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c246 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 82, Sat.Literal.neg 60] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (1 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c247 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 47, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (1 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c248 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 83, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (1 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c249 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.neg 87, Sat.Literal.neg 18] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c250 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 15, Sat.Literal.neg 54] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c251 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 52, Sat.Literal.neg 96] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c252 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.neg 88, Sat.Literal.neg 24] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c253 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 16, Sat.Literal.neg 60] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c254 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 52, Sat.Literal.neg 24] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c255 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 53, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (2 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c256 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 58, Sat.Literal.neg 96] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c257 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 94, Sat.Literal.neg 60] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c258 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.neg 22, Sat.Literal.neg 96] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c259 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.neg 94, Sat.Literal.neg 24] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c260 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 22, Sat.Literal.neg 60] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c261 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 58, Sat.Literal.neg 24] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c262 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 59, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c263 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 95, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c264 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.neg 23, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c265 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 23, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c266 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 59, Sat.Literal.neg 30] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c267 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 65, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c268 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 101, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c269 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 40, Sat.Literal.neg 29, Sat.Literal.neg 102] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c270 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 40, Sat.Literal.neg 101, Sat.Literal.neg 30] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c271 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.neg 29, Sat.Literal.neg 66] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c272 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 51, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c273 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 87, Sat.Literal.neg 55] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c274 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 15, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c275 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 87, Sat.Literal.neg 19] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c276 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 52, Sat.Literal.neg 97] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c277 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 88, Sat.Literal.neg 61] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c278 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 16, Sat.Literal.neg 97] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c279 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 88, Sat.Literal.neg 25] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c280 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 53, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c281 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 8, Sat.Literal.neg 89, Sat.Literal.neg 67] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (2 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c282 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 17, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (2 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c283 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 89, Sat.Literal.neg 31] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (2 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c284 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 58, Sat.Literal.neg 97] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c285 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 94, Sat.Literal.neg 61] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c286 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 22, Sat.Literal.neg 97] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c287 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 94, Sat.Literal.neg 25] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c288 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 81, Sat.Literal.neg 22, Sat.Literal.neg 61] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c289 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 81, Sat.Literal.neg 58, Sat.Literal.neg 25] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c290 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 59, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c291 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 95, Sat.Literal.neg 67] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c292 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 23, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c293 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 95, Sat.Literal.neg 31] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c294 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 81, Sat.Literal.neg 23, Sat.Literal.neg 67] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c295 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 81, Sat.Literal.neg 59, Sat.Literal.neg 31] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c296 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 65, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c297 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 101, Sat.Literal.neg 67] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c298 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.neg 29, Sat.Literal.neg 103] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c299 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.neg 101, Sat.Literal.neg 31] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c300 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 29, Sat.Literal.neg 67] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c301 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 65, Sat.Literal.neg 31] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c302 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.neg 58, Sat.Literal.neg 98] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c303 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.neg 94, Sat.Literal.neg 62] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c304 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 22, Sat.Literal.neg 98] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c305 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 94, Sat.Literal.neg 26] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c306 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 87, Sat.Literal.neg 22, Sat.Literal.neg 62] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c307 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.neg 59, Sat.Literal.neg 104] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c308 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.neg 95, Sat.Literal.neg 68] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c309 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 23, Sat.Literal.neg 104] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c310 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 95, Sat.Literal.neg 32] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 6) (3 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c311 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 16, Sat.Literal.neg 65, Sat.Literal.neg 104] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c312 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 16, Sat.Literal.neg 101, Sat.Literal.neg 68] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c313 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 29, Sat.Literal.neg 104] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c314 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 101, Sat.Literal.neg 32] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c315 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.neg 29, Sat.Literal.neg 68] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c316 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.neg 65, Sat.Literal.neg 32] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c317 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.neg 65, Sat.Literal.neg 105] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c318 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.neg 101, Sat.Literal.neg 69] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c319 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 29, Sat.Literal.neg 105] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c320 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 101, Sat.Literal.neg 33] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c321 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.neg 29, Sat.Literal.neg 69] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c322 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.neg 65, Sat.Literal.neg 33] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n6_c323 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 1, Sat.Literal.pos 216] :=
  h.first_advance_clause 0 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c324 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 73, Sat.Literal.neg 73] :=
  h.first_conflict_clause 0 (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c325 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 216, Sat.Literal.neg 8, Sat.Literal.neg 8, Sat.Literal.pos 217] :=
  h.advance_clause 0 (0 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c326 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 216, Sat.Literal.neg 80, Sat.Literal.neg 80] :=
  h.conflict_clause 0 (0 : Fin 5) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c327 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 217, Sat.Literal.neg 15, Sat.Literal.neg 15, Sat.Literal.pos 218] :=
  h.advance_clause 0 (1 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c328 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 217, Sat.Literal.neg 87, Sat.Literal.neg 87] :=
  h.conflict_clause 0 (1 : Fin 5) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c329 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 218, Sat.Literal.neg 22, Sat.Literal.neg 22, Sat.Literal.pos 219] :=
  h.advance_clause 0 (2 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c330 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 218, Sat.Literal.neg 94, Sat.Literal.neg 94] :=
  h.conflict_clause 0 (2 : Fin 5) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c331 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 219, Sat.Literal.neg 101, Sat.Literal.neg 101] :=
  h.conflict_clause 0 (3 : Fin 5) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c332 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 37, Sat.Literal.neg 37] :=
  h.first_conflict_clause 1 (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c333 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 44, Sat.Literal.pos 251] :=
  h.first_advance_clause 7 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c334 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 251, Sat.Literal.neg 44, Sat.Literal.neg 51] :=
  h.conflict_clause 7 (0 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c335 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 44, Sat.Literal.pos 261] :=
  h.first_advance_clause 9 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c336 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 261, Sat.Literal.neg 44, Sat.Literal.neg 87, Sat.Literal.pos 262] :=
  h.advance_clause 9 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c337 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 262, Sat.Literal.neg 87, Sat.Literal.neg 58] :=
  h.conflict_clause 9 (1 : Fin 5) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c338 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 15, Sat.Literal.pos 271] :=
  h.first_advance_clause 11 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c339 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 271, Sat.Literal.neg 44, Sat.Literal.neg 22] :=
  h.conflict_clause 11 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c340 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 51, Sat.Literal.pos 281] :=
  h.first_advance_clause 13 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c341 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 281, Sat.Literal.neg 8, Sat.Literal.neg 58, Sat.Literal.pos 282] :=
  h.advance_clause 13 (0 : Fin 5) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n6_c342 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 282, Sat.Literal.neg 51, Sat.Literal.neg 29, Sat.Literal.pos 283] :=
  h.advance_clause 13 (1 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c343 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 282, Sat.Literal.neg 51, Sat.Literal.neg 65] :=
  h.conflict_clause 13 (1 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c344 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 283, Sat.Literal.neg 58, Sat.Literal.neg 66] :=
  h.conflict_clause 13 (2 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c345 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 87, Sat.Literal.pos 286] :=
  h.first_advance_clause 14 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c346 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 44, Sat.Literal.neg 22, Sat.Literal.pos 287] :=
  h.advance_clause 14 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c347 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 44, Sat.Literal.neg 94] :=
  h.conflict_clause 14 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c348 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 287, Sat.Literal.neg 87, Sat.Literal.neg 101] :=
  h.conflict_clause 14 (1 : Fin 5) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c349 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 51, Sat.Literal.pos 291] :=
  h.first_advance_clause 15 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c350 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 291, Sat.Literal.neg 8, Sat.Literal.neg 58, Sat.Literal.pos 292] :=
  h.advance_clause 15 (0 : Fin 5) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n6_c351 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 292, Sat.Literal.neg 51, Sat.Literal.neg 101, Sat.Literal.pos 293] :=
  h.advance_clause 15 (1 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c352 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 293, Sat.Literal.neg 58, Sat.Literal.neg 66] :=
  h.conflict_clause 15 (2 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c353 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 87, Sat.Literal.pos 296] :=
  h.first_advance_clause 16 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c354 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 296, Sat.Literal.neg 44, Sat.Literal.neg 94] :=
  h.conflict_clause 16 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c355 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 22, Sat.Literal.pos 301] :=
  h.first_advance_clause 17 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c356 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 301, Sat.Literal.neg 44, Sat.Literal.neg 29] :=
  h.conflict_clause 17 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c357 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 58, Sat.Literal.pos 311] :=
  h.first_advance_clause 19 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c358 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 311, Sat.Literal.neg 8, Sat.Literal.neg 65, Sat.Literal.pos 312] :=
  h.advance_clause 19 (0 : Fin 5) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n6_c359 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 311, Sat.Literal.neg 44, Sat.Literal.neg 65] :=
  h.conflict_clause 19 (0 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c360 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 312, Sat.Literal.neg 51, Sat.Literal.neg 66] :=
  h.conflict_clause 19 (1 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c361 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 94, Sat.Literal.pos 316] :=
  h.first_advance_clause 20 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c362 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 316, Sat.Literal.neg 8, Sat.Literal.neg 101, Sat.Literal.pos 317] :=
  h.advance_clause 20 (0 : Fin 5) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c363 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 316, Sat.Literal.neg 44, Sat.Literal.neg 29, Sat.Literal.pos 317] :=
  h.advance_clause 20 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c364 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 316, Sat.Literal.neg 44, Sat.Literal.neg 101] :=
  h.conflict_clause 20 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c365 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 317, Sat.Literal.neg 15, Sat.Literal.neg 102, Sat.Literal.pos 318] :=
  h.advance_clause 20 (1 : Fin 5) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c366 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 317, Sat.Literal.neg 51, Sat.Literal.neg 102] :=
  h.conflict_clause 20 (1 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c367 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 318, Sat.Literal.neg 94, Sat.Literal.neg 1] :=
  h.conflict_clause 20 (2 : Fin 5) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c368 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 29, Sat.Literal.pos 331] :=
  h.first_advance_clause 23 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c369 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 331, Sat.Literal.neg 8, Sat.Literal.neg 30, Sat.Literal.pos 332] :=
  h.advance_clause 23 (0 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c370 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 331, Sat.Literal.neg 44, Sat.Literal.neg 30] :=
  h.conflict_clause 23 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c371 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 332, Sat.Literal.neg 15, Sat.Literal.neg 1, Sat.Literal.pos 333] :=
  h.advance_clause 23 (1 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c372 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 332, Sat.Literal.neg 51, Sat.Literal.neg 1] :=
  h.conflict_clause 23 (1 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c373 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 333, Sat.Literal.neg 58, Sat.Literal.neg 8] :=
  h.conflict_clause 23 (2 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c374 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 29, Sat.Literal.pos 336] :=
  h.first_advance_clause 24 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c375 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 336, Sat.Literal.neg 44, Sat.Literal.neg 102, Sat.Literal.pos 337] :=
  h.advance_clause 24 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c376 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 337, Sat.Literal.neg 87, Sat.Literal.neg 1] :=
  h.conflict_clause 24 (1 : Fin 5) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c377 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 65, Sat.Literal.pos 341] :=
  h.first_advance_clause 25 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c378 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 341, Sat.Literal.neg 8, Sat.Literal.neg 66, Sat.Literal.pos 342] :=
  h.advance_clause 25 (0 : Fin 5) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n6_c379 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 341, Sat.Literal.neg 44, Sat.Literal.neg 66] :=
  h.conflict_clause 25 (0 : Fin 5) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c380 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 342, Sat.Literal.neg 51, Sat.Literal.neg 1, Sat.Literal.pos 343] :=
  h.advance_clause 25 (1 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c381 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 343, Sat.Literal.neg 94, Sat.Literal.neg 8] :=
  h.conflict_clause 25 (2 : Fin 5) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c382 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 101, Sat.Literal.pos 346] :=
  h.first_advance_clause 26 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c383 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 346, Sat.Literal.neg 8, Sat.Literal.neg 102, Sat.Literal.pos 347] :=
  h.advance_clause 26 (0 : Fin 5) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n6_c384 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 346, Sat.Literal.neg 44, Sat.Literal.neg 102] :=
  h.conflict_clause 26 (0 : Fin 5) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n6_c385 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 347, Sat.Literal.neg 51, Sat.Literal.neg 1, Sat.Literal.pos 348] :=
  h.advance_clause 26 (1 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c386 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 348, Sat.Literal.neg 94, Sat.Literal.neg 8] :=
  h.conflict_clause 26 (2 : Fin 5) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c387 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 30, Sat.Literal.pos 361] :=
  h.first_advance_clause 29 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c388 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 361, Sat.Literal.neg 8, Sat.Literal.neg 1, Sat.Literal.pos 362] :=
  h.advance_clause 29 (0 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c389 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 361, Sat.Literal.neg 44, Sat.Literal.neg 1] :=
  h.conflict_clause 29 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c390 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 362, Sat.Literal.neg 15, Sat.Literal.neg 8, Sat.Literal.pos 363] :=
  h.advance_clause 29 (1 : Fin 5) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c391 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 362, Sat.Literal.neg 51, Sat.Literal.neg 8] :=
  h.conflict_clause 29 (1 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c392 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 363, Sat.Literal.neg 58, Sat.Literal.neg 15] :=
  h.conflict_clause 29 (2 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c393 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 66, Sat.Literal.pos 371] :=
  h.first_advance_clause 31 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c394 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 371, Sat.Literal.neg 44, Sat.Literal.neg 1, Sat.Literal.pos 372] :=
  h.advance_clause 31 (0 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c395 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 372, Sat.Literal.neg 15, Sat.Literal.neg 44, Sat.Literal.pos 373] :=
  h.advance_clause 31 (1 : Fin 5) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n6_c396 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 372, Sat.Literal.neg 87, Sat.Literal.neg 44] :=
  h.conflict_clause 31 (1 : Fin 5) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n6_c397 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 373, Sat.Literal.neg 58, Sat.Literal.neg 15, Sat.Literal.pos 374] :=
  h.advance_clause 31 (2 : Fin 5) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n6_c398 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 373, Sat.Literal.neg 94, Sat.Literal.neg 15] :=
  h.conflict_clause 31 (2 : Fin 5) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n6_c399 (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) :
    val.satisfies [Sat.Literal.neg 374, Sat.Literal.neg 101, Sat.Literal.neg 58] :=
  h.conflict_clause 31 (3 : Fin 5) (2 : Fin 3) (1 : Fin 3) (by decide)

lrat_proof cert_n6_root
  "p cnf 391 400\n3 13 39 49 75 85 0\n4 19 40 55 76 91 0\n5 25 41 61 77 97 0\n6 31 42 67 78 103 0\n9 14 45 50 81 86 0\n10 20 46 56 82 92 0\n11 26 47 62 83 98 0\n-62 -98 0\n12 32 48 68 84 104 0\n16 21 52 57 88 93 0\n17 27 53 63 89 99 0\n18 33 54 69 90 105 0\n23 28 59 64 95 100 0\n-23 -59 0\n-23 -95 0\n24 34 60 70 96 106 0\n-24 -60 0\n30 35 66 71 102 107 0\n-2 110 0\n-3 111 0\n-4 112 0\n-5 113 0\n-6 114 0\n-9 117 0\n-10 118 0\n-11 119 0\n-12 120 0\n-13 121 0\n-14 122 0\n-16 124 0\n-17 125 0\n-18 126 0\n-19 127 0\n-20 128 0\n-21 129 0\n-23 131 0\n-24 132 0\n-25 133 0\n-26 134 0\n-27 135 0\n-28 136 0\n-30 138 0\n-31 139 0\n-32 140 0\n-33 141 0\n-34 142 0\n-35 143 0\n-110 -117 111 0\n-110 -118 112 0\n-110 -120 114 0\n-111 -126 114 0\n-112 -132 114 0\n-113 -138 114 0\n-117 -124 118 0\n-117 -125 119 0\n-117 -126 120 0\n-118 -131 119 0\n-118 -132 120 0\n-119 -138 120 0\n-121 -110 122 0\n-124 -127 121 0\n-124 -128 122 0\n-124 -131 125 0\n-124 -132 126 0\n-125 -133 121 0\n-125 -134 122 0\n-125 -138 126 0\n-126 -140 122 0\n-127 -111 129 0\n-128 -117 129 0\n-131 -133 127 0\n-131 -134 128 0\n-131 -135 129 0\n-131 -138 132 0\n-132 -140 128 0\n-132 -141 129 0\n-133 -110 134 0\n-133 -111 135 0\n-133 -112 136 0\n-134 -117 135 0\n-134 -118 136 0\n-135 -124 136 0\n-138 -140 134 0\n-138 -141 135 0\n-138 -142 136 0\n-139 -110 140 0\n-140 -117 141 0\n-140 -118 142 0\n-140 -119 143 0\n-141 -124 142 0\n-141 -125 143 0\n-142 -131 143 0\n-39 147 0\n-40 148 0\n-41 149 0\n-42 150 0\n-45 153 0\n-46 154 0\n-47 155 0\n-48 156 0\n-49 157 0\n-50 158 0\n-52 160 0\n-53 161 0\n-54 162 0\n-55 163 0\n-56 164 0\n-57 165 0\n-59 167 0\n-60 168 0\n-61 169 0\n-62 170 0\n-63 171 0\n-64 172 0\n-66 174 0\n-67 175 0\n-68 176 0\n-69 177 0\n-70 178 0\n-71 179 0\n-147 -161 149 0\n-147 -162 150 0\n-148 -167 149 0\n-148 -168 150 0\n-149 -174 150 0\n-153 -157 151 0\n-154 -163 151 0\n-154 -168 156 0\n-155 -169 151 0\n-155 -174 156 0\n-156 -175 151 0\n-160 -164 158 0\n-161 -169 157 0\n-161 -170 158 0\n-161 -174 162 0\n-162 -176 158 0\n-164 -153 165 0\n-167 -169 163 0\n-167 -170 164 0\n-167 -171 165 0\n-168 -176 164 0\n-168 -177 165 0\n-169 -148 172 0\n-170 -153 171 0\n-170 -154 172 0\n-171 -160 172 0\n-174 -175 169 0\n-174 -176 170 0\n-174 -177 171 0\n-174 -178 172 0\n-175 -148 178 0\n-175 -149 179 0\n-176 -153 177 0\n-176 -154 178 0\n-176 -155 179 0\n-177 -160 178 0\n-177 -161 179 0\n-178 -167 179 0\n-75 183 0\n-76 184 0\n-77 185 0\n-78 186 0\n-82 190 0\n-83 191 0\n-84 192 0\n-86 194 0\n-88 196 0\n-89 197 0\n-90 198 0\n-91 199 0\n-92 200 0\n-93 201 0\n-95 203 0\n-96 204 0\n-97 205 0\n-98 206 0\n-99 207 0\n-100 208 0\n-102 210 0\n-103 211 0\n-104 212 0\n-105 213 0\n-106 214 0\n-107 215 0\n-183 -197 185 0\n-184 -203 185 0\n-184 -204 186 0\n-185 -210 186 0\n-190 -199 187 0\n-190 -203 191 0\n-190 -204 192 0\n-191 -205 187 0\n-191 -210 192 0\n-192 -211 187 0\n-196 -200 194 0\n-197 -206 194 0\n-197 -210 198 0\n-198 -212 194 0\n-199 -183 201 0\n-203 -205 199 0\n-203 -207 201 0\n-203 -210 204 0\n-204 -211 199 0\n-204 -212 200 0\n-204 -213 201 0\n-205 -183 207 0\n-205 -184 208 0\n-206 -190 208 0\n-207 -196 208 0\n-210 -211 205 0\n-210 -212 206 0\n-210 -213 207 0\n-210 -214 208 0\n-211 -183 213 0\n-211 -184 214 0\n-211 -185 215 0\n-212 -190 214 0\n-212 -191 215 0\n-213 -197 215 0\n-214 -203 215 0\n-114 0\n-150 0\n-186 0\n2 38 74 0\n-151 0\n-187 0\n9 45 81 0\n-122 0\n-158 0\n-194 0\n16 52 88 0\n-129 0\n-165 0\n-201 0\n23 59 95 0\n-136 0\n-172 0\n-208 0\n30 66 102 0\n-143 0\n-179 0\n-215 0\n-2 -45 -85 0\n-2 -46 -91 0\n-2 -82 -55 0\n-2 -47 -97 0\n-2 -83 -61 0\n-2 -48 -103 0\n-2 -84 -67 0\n-39 -88 -19 0\n-75 -16 -55 0\n-3 -53 -97 0\n-39 -89 -25 0\n-75 -17 -61 0\n-75 -53 -25 0\n-3 -54 -103 0\n-4 -59 -97 0\n-4 -95 -61 0\n-40 -23 -97 0\n-40 -95 -25 0\n-76 -23 -61 0\n-76 -59 -25 0\n-4 -60 -103 0\n-4 -96 -67 0\n-40 -24 -103 0\n-76 -24 -67 0\n-76 -60 -31 0\n-5 -66 -103 0\n-5 -102 -67 0\n-41 -30 -103 0\n-41 -102 -31 0\n-77 -30 -67 0\n-9 -52 -92 0\n-9 -88 -56 0\n-45 -16 -92 0\n-45 -88 -20 0\n-9 -53 -98 0\n-9 -89 -62 0\n-45 -17 -98 0\n-45 -89 -26 0\n-9 -54 -104 0\n-9 -90 -68 0\n-45 -18 -104 0\n-45 -90 -32 0\n-10 -59 -98 0\n-10 -95 -62 0\n-46 -23 -98 0\n-46 -95 -26 0\n-82 -23 -62 0\n-82 -59 -26 0\n-10 -60 -104 0\n-10 -96 -68 0\n-46 -24 -104 0\n-46 -96 -32 0\n-82 -24 -68 0\n-82 -60 -32 0\n-11 -66 -104 0\n-11 -102 -68 0\n-47 -30 -104 0\n-47 -102 -32 0\n-83 -30 -68 0\n-83 -66 -32 0\n-16 -59 -99 0\n-16 -95 -63 0\n-52 -23 -99 0\n-52 -95 -27 0\n-88 -23 -63 0\n-16 -60 -105 0\n-16 -96 -69 0\n-52 -24 -105 0\n-52 -96 -33 0\n-17 -66 -105 0\n-17 -102 -69 0\n-53 -30 -105 0\n-53 -102 -33 0\n-89 -30 -69 0\n-89 -66 -33 0\n-23 -66 -106 0\n-23 -102 -70 0\n-59 -30 -106 0\n-59 -102 -34 0\n-95 -30 -70 0\n-95 -66 -34 0\n-2 -2 217 0\n-74 -74 0\n-217 -9 -9 218 0\n-217 -81 -81 0\n-218 -16 -16 219 0\n-218 -88 -88 0\n-219 -23 -23 220 0\n-219 -95 -95 0\n-220 -102 -102 0\n-38 -38 0\n-2 -45 252 0\n-252 -45 -52 0\n-2 -45 262 0\n-262 -45 -88 263 0\n-263 -88 -59 0\n-2 -16 272 0\n-272 -45 -23 0\n-2 -52 282 0\n-282 -9 -59 283 0\n-283 -52 -30 284 0\n-283 -52 -66 0\n-284 -59 -67 0\n-2 -88 287 0\n-287 -45 -23 288 0\n-287 -45 -95 0\n-288 -88 -102 0\n-2 -52 292 0\n-292 -9 -59 293 0\n-293 -52 -102 294 0\n-294 -59 -67 0\n-2 -88 297 0\n-297 -45 -95 0\n-2 -23 302 0\n-302 -45 -30 0\n-2 -59 312 0\n-312 -9 -66 313 0\n-312 -45 -66 0\n-313 -52 -67 0\n-2 -95 317 0\n-317 -9 -102 318 0\n-317 -45 -30 318 0\n-317 -45 -102 0\n-318 -16 -103 319 0\n-318 -52 -103 0\n-319 -95 -2 0\n-2 -30 332 0\n-332 -9 -31 333 0\n-332 -45 -31 0\n-333 -16 -2 334 0\n-333 -52 -2 0\n-334 -59 -9 0\n-2 -30 337 0\n-337 -45 -103 338 0\n-338 -88 -2 0\n-2 -66 342 0\n-342 -9 -67 343 0\n-342 -45 -67 0\n-343 -52 -2 344 0\n-344 -95 -9 0\n-2 -102 347 0\n-347 -9 -103 348 0\n-347 -45 -103 0\n-348 -52 -2 349 0\n-349 -95 -9 0\n-2 -31 362 0\n-362 -9 -2 363 0\n-362 -45 -2 0\n-363 -16 -9 364 0\n-363 -52 -9 0\n-364 -59 -16 0\n-2 -67 372 0\n-372 -45 -2 373 0\n-373 -16 -45 374 0\n-373 -88 -45 0\n-374 -59 -16 375 0\n-374 -95 -16 0\n-375 -102 -59 0\n"
  "401 -6 0 221 23 0\n402 -42 0 222 96 0\n403 -78 0 223 162 0\n404 -14 0 228 29 0\n405 -50 0 229 102 0\n406 -86 0 230 166 0\n407 -21 0 232 35 0\n408 -57 0 233 108 0\n409 -93 0 234 172 0\n410 -28 0 236 41 0\n411 -64 0 237 114 0\n412 -100 0 238 178 0\n413 -35 0 240 47 0\n414 -71 0 241 120 0\n415 -107 0 242 184 0\n416 -2 217 0 324 0\n417 -74 0 325 0\n418 -217 -9 218 0 326 0\n419 -217 -81 0 327 0\n420 -218 -16 219 0 328 0\n421 -218 -88 0 329 0\n422 -219 -23 220 0 330 0\n423 -219 -95 0 331 0\n424 -220 -102 0 332 0\n425 -38 0 333 0\n426 2 0 425 417 224 0\n427 110 0 426 19 0\n428 217 0 426 416 0\n429 -120 0 427 221 50 0\n430 -121 0 427 228 60 0\n431 -81 0 428 419 0\n432 -12 0 429 27 0\n433 -13 0 430 28 0\n434 -45 252 0 426 334 0\n435 -45 262 0 426 336 0\n436 -16 272 0 426 339 0\n437 -52 282 0 426 341 0\n438 -88 287 0 426 346 0\n439 -52 292 0 426 350 0\n440 -88 297 0 426 354 0\n441 -23 302 0 426 356 0\n442 -59 312 0 426 358 0\n443 -95 317 0 426 362 0\n444 -319 -95 0 426 368 0\n445 -30 332 0 426 369 0\n446 -333 -16 334 0 426 372 0\n447 -333 -52 0 426 373 0\n448 -30 337 0 426 375 0\n449 -338 -88 0 426 377 0\n450 -66 342 0 426 378 0\n451 -343 -52 344 0 426 381 0\n452 -102 347 0 426 383 0\n453 -348 -52 349 0 426 386 0\n454 -31 362 0 426 388 0\n455 -362 -9 363 0 426 389 0\n456 -362 -45 0 426 390 0\n457 -67 372 0 426 394 0\n458 -372 -45 373 0 426 395 0\n459 -54 32 -9 -67 0 426 225 229 432 116 131 100 249 105 281 136 9 117 0\n460 -90 32 -9 -67 0 426 225 230 432 116 131 100 249 169 282 198 9 181 0\n461 -69 63 99 17 27 -30 0 241 118 316 157 11 104 0\n462 -46 4 76 19 40 0 426 225 98 244 127 2 106 0\n463 -105 99 70 63 40 -16 106 -67 -30 0 430 228 236 234 242 221 429 406 431 405 404 233 426 226 30 82 40 62 34 61 33 42 85 46 59 182 308 314 205 219 174 168 16 11 37 266 31 52 58 55 21 25 24 5 97 275 137 107 462 6 163 245 189 2 170 0\n464 -91 56 92 10 20 0 426 226 170 244 189 6 163 0\n465 -82 91 62 4 19 40 -59 41 77 -138 0 221 429 238 426 225 59 26 53 22 163 245 290 208 2 176 160 262 207 175 3 111 247 129 7 99 0\n466 112 -16 106 -59 77 -67 -138 0 236 225 241 430 228 427 406 431 405 404 233 223 30 62 34 61 33 109 158 119 116 152 123 94 140 95 131 85 46 21 49 25 54 24 5 97 275 137 144 107 112 464 465 6 98 462 128 160 266 110 187 16 174 0\n467 -46 24 19 70 40 106 -67 34 0 225 223 116 131 98 128 110 16 174 264 187 462 160 0\n468 -60 32 -10 105 33 -67 0 426 225 233 432 229 431 429 116 131 100 249 110 291 142 9 118 117 136 153 105 97 227 24 460 56 12 32 0\n469 -10 -16 -59 -67 -30 0 426 225 233 241 221 236 432 230 242 431 429 42 272 320 466 52 37 116 152 109 123 94 140 113 158 119 303 463 85 30 90 45 131 100 249 46 59 26 25 285 81 88 39 44 468 16 292 309 9 181 299 198 218 169 164 7 112 144 97 227 24 459 56 12 32 0\n470 -9 105 27 141 99 63 -67 -30 0 429 45 42 59 24 56 55 87 32 31 44 461 459 460 12 0\n471 -82 91 62 25 19 40 -59 41 77 -138 0 221 429 238 426 225 59 26 53 22 163 290 465 208 257 176 3 111 247 129 7 99 0\n472 -31 59 0 427 240 431 428 43 454 86 456 89 227 24 418 455 55 421 392 231 30 420 63 423 36 235 0\n473 -45 -16 59 -372 0 412 411 410 436 458 340 396 13 399 0\n474 -105 27 99 63 17 -30 0 242 182 314 219 11 168 0\n475 -76 25 -23 77 41 5 0 238 160 261 207 3 175 0\n476 40 76 10 4 56 92 19 20 0 426 464 462 2 6 245 0\n477 -23 -16 119 0 431 436 30 36 340 57 227 54 24 0\n478 -98 63 99 17 -9 27 0 230 176 277 196 11 168 0\n479 -62 63 99 17 -9 27 0 229 112 278 134 11 104 0\n480 -47 25 77 41 5 0 426 225 99 246 129 3 111 0\n481 -9 -16 77 41 -138 0 221 236 429 428 427 233 426 226 59 477 30 82 40 26 53 22 24 418 48 55 80 420 78 31 39 423 38 235 109 303 140 113 478 479 480 7 164 247 192 3 175 0\n482 -96 10 -32 56 92 20 192 0 174 294 191 6 163 0\n483 -70 23 -30 0 241 119 322 158 235 109 0\n484 10 62 -59 40 4 56 92 20 19 77 41 -138 0 221 238 225 109 53 22 464 476 465 160 262 6 207 98 175 127 3 138 111 0\n485 -10 68 -60 -103 142 0 426 226 432 180 194 165 248 25 291 88 9 44 0\n486 -60 164 92 23 20 19 41 -103 -138 0 236 242 222 107 180 216 161 85 110 263 124 141 94 117 485 476 160 186 173 235 109 484 139 112 0\n487 -54 75 49 85 -103 0 222 433 105 256 122 1 93 0\n488 -95 -16 -103 -30 0 242 404 405 431 406 42 270 180 216 161 481 5 443 444 364 366 0\n489 -89 47 83 62 -45 11 0 230 168 280 196 7 176 0\n490 -68 62 63 99 -45 27 -30 0 429 241 228 97 42 59 26 117 301 153 155 157 99 104 489 11 31 279 66 7 39 0\n491 -104 -46 105 69 106 60 70 -45 33 -103 34 0 426 225 230 234 97 126 101 243 180 181 293 283 198 16 169 174 12 205 487 214 159 0\n492 -26 99 -59 60 70 92 -45 33 27 128 -103 -30 0 426 226 233 228 236 432 109 140 113 97 137 139 112 490 320 107 34 180 194 165 248 42 85 46 39 290 66 81 31 25 461 474 6 491 9 44 294 75 16 37 0\n493 -32 106 60 70 56 92 128 192 142 0 34 46 44 88 75 25 37 482 16 0\n494 135 98 62 77 41 -117 -138 0 221 429 427 426 226 48 59 26 53 22 80 78 39 38 480 7 164 247 192 3 175 0\n495 -83 32 84 48 -30 0 242 432 164 301 218 9 181 0\n496 -33 60 -52 70 106 34 0 232 45 311 76 16 37 0\n497 -54 32 84 48 -9 0 229 432 105 281 136 9 117 0\n498 -90 32 84 48 -9 0 230 432 169 282 198 9 181 0\n499 -103 -59 -9 -30 0 236 428 429 427 232 241 426 226 242 409 408 407 229 234 109 158 14 483 320 24 48 69 33 70 34 56 32 418 421 42 85 46 180 248 270 194 216 165 161 481 10 103 273 132 156 107 486 118 493 496 497 498 12 182 310 205 16 174 0\n500 -105 60 70 106 -9 34 0 429 428 234 418 421 24 56 182 205 174 16 37 310 64 231 30 0\n501 -16 105 -59 -9 -30 0 233 236 403 402 401 499 109 140 113 374 42 85 445 30 303 446 82 90 370 40 470 4 0\n502 -52 -59 -9 -30 0 403 402 401 499 445 437 447 342 370 343 4 345 0\n503 -59 -9 -30 0 236 428 418 421 42 85 46 14 320 483 502 231 501 308 500 0\n504 59 -16 -45 -30 0 412 411 410 403 402 401 357 441 445 371 473 13 457 488 4 0\n505 -67 62 -59 92 70 -16 56 -30 0 430 228 241 221 236 109 158 320 30 62 34 61 33 42 85 46 116 272 469 466 152 151 464 52 79 95 94 37 38 467 471 6 0\n506 -105 34 106 -16 -9 70 0 308 500 0\n507 -32 98 26 27 99 63 -9 47 -66 0 240 24 44 302 89 26 55 7 31 479 0\n508 -62 54 105 -59 -66 -67 0 225 429 233 428 236 431 240 450 380 227 24 418 421 442 359 361 231 30 82 80 39 40 303 115 109 140 149 118 113 56 32 116 131 130 99 8 479 507 31 460 91 12 45 0\n509 32 54 105 -59 -66 -67 0 426 225 429 233 428 236 431 240 229 432 242 508 450 380 227 24 418 421 442 359 361 231 30 82 80 39 40 303 115 109 140 149 118 113 56 32 116 131 130 99 100 249 460 12 45 317 91 31 478 11 104 134 148 117 9 181 297 218 7 164 0\n510 32 105 -59 -66 -67 0 431 450 380 227 459 509 0\n511 -32 26 27 99 63 -9 47 -66 0 240 24 44 507 89 478 55 31 0\n512 -59 -66 -67 0 426 225 431 428 233 236 229 432 242 450 380 227 418 421 24 116 131 115 130 99 100 249 109 442 140 359 113 361 231 30 303 82 40 80 39 511 510 182 312 219 479 478 168 11 104 134 148 117 9 181 297 218 7 164 0\n513 -16 106 -23 -9 70 -67 0 429 240 233 36 92 46 24 56 32 30 477 506 64 90 89 37 45 44 459 460 12 118 309 142 16 110 0\n514 -45 102 -59 23 -16 0 430 228 241 233 415 414 413 429 236 403 402 401 426 226 432 238 109 158 119 140 113 303 442 30 82 40 62 34 61 33 97 456 360 275 137 144 454 18 107 112 42 320 490 505 59 85 84 4 26 46 45 180 248 270 486 492 194 165 493 495 9 299 7 176 285 279 208 461 474 163 491 6 0\n515 -103 105 69 -52 -9 106 70 -30 23 0 236 429 427 232 229 426 226 103 132 107 273 24 48 69 33 70 34 56 32 42 85 46 180 248 270 486 194 496 165 493 497 498 12 0\n516 32 -67 105 69 -52 -9 34 214 70 0 429 232 229 426 225 432 116 131 100 249 103 132 107 273 24 70 34 56 32 183 459 460 12 496 110 128 141 98 117 9 181 291 217 6 163 0\n517 -60 10 -32 156 56 92 20 0 110 296 128 6 98 0\n518 -9 -30 -95 31 23 16 0 429 234 242 221 236 428 427 229 403 402 401 225 241 232 223 226 237 42 85 46 53 22 173 220 183 201 177 59 322 24 418 48 70 55 421 69 34 31 231 33 103 273 306 132 146 107 113 461 474 515 4 116 272 470 131 152 76 95 37 516 44 88 25 517 16 174 264 294 187 6 160 163 476 189 94 260 200 143 175 111 3 0\n519 -30 -95 16 31 23 0 407 408 409 404 405 431 406 518 5 434 348 335 438 10 0\n520 -45 -59 16 0 409 408 407 434 435 335 10 337 338 0\n521 -23 -67 -30 -52 -9 0 237 429 232 24 56 42 67 31 103 146 113 36 305 73 40 84 474 470 0\n522 23 -30 59 16 0 412 411 410 472 13 519 0\n523 -45 -59 -16 0 403 402 401 14 456 514 454 452 400 385 398 4 396 457 458 0\n524 -69 -102 -59 -16 0 241 431 429 238 233 179 213 183 321 30 523 227 24 56 64 37 109 158 119 118 309 142 16 110 0\n525 -83 77 5 41 25 0 426 226 164 247 192 3 175 0\n526 32 33 69 105 -67 -9 0 429 24 56 32 459 460 12 0\n527 119 83 47 26 -9 63 99 27 0 24 26 55 31 479 478 7 0\n528 -67 -59 -16 0 233 431 427 236 426 225 241 415 414 413 223 238 240 230 432 30 82 523 227 24 48 78 38 80 39 503 109 158 119 140 113 303 40 116 249 512 131 152 18 100 95 179 321 269 188 213 161 183 480 506 524 525 527 89 44 526 45 315 91 31 478 479 11 7 168 298 196 9 211 181 0\n529 -102 17 -11 32 -59 -16 0 236 233 241 429 226 401 402 403 426 431 238 432 230 523 227 393 391 455 454 528 4 248 180 194 165 498 497 24 56 32 109 158 119 140 113 303 30 82 40 179 321 524 298 213 9 183 181 506 198 12 197 315 168 11 0\n530 17 -11 32 -59 -16 0 236 233 429 226 401 402 403 426 431 432 229 242 523 227 393 391 455 454 528 4 248 180 194 165 498 497 24 56 32 503 109 140 113 303 30 82 40 529 239 115 297 149 9 118 117 136 135 104 11 168 317 219 12 182 0\n531 -66 -17 90 54 18 171 0 240 31 91 45 115 312 149 12 118 0\n532 -17 32 -59 -16 0 233 241 429 226 401 402 403 426 431 240 415 414 413 238 523 227 393 391 455 454 528 4 248 180 194 165 498 497 24 56 32 503 109 158 119 140 31 91 45 531 18 179 321 524 213 12 183 506 0\n533 -83 41 -103 25 30 0 226 242 415 414 413 180 216 161 194 164 525 193 268 179 18 0\n534 41 62 98 32 -59 -16 0 233 429 427 236 242 226 401 402 403 426 431 241 415 414 413 432 238 230 532 530 523 227 393 391 455 454 528 4 248 180 194 165 498 497 216 161 30 82 24 48 78 38 80 39 56 32 503 109 158 119 140 113 303 40 533 7 99 480 155 268 117 18 9 179 321 524 181 213 198 183 197 506 168 12 11 315 0\n535 62 98 32 -59 -16 0 233 429 236 226 401 402 403 426 431 222 415 414 413 238 241 432 230 532 530 523 227 393 391 455 454 528 4 248 180 194 165 498 497 30 82 24 80 39 56 32 503 109 158 119 140 113 303 40 534 95 125 115 18 179 321 524 213 193 183 164 506 7 12 99 315 155 11 117 168 9 196 181 211 0\n536 32 -59 -16 0 236 233 431 523 227 109 140 113 303 30 82 40 532 479 478 535 0\n537 -102 62 98 -32 192 26 0 240 44 89 26 179 300 193 7 164 0\n538 -59 -16 0 236 233 431 427 403 402 401 226 242 240 222 30 82 40 109 303 393 140 113 523 227 24 503 391 48 80 455 78 39 454 38 528 4 180 194 216 161 536 44 89 55 31 478 479 537 239 115 268 511 125 480 95 0\n539 -9 -16 0 428 429 240 237 403 402 401 426 226 233 538 472 30 24 418 56 420 32 64 423 37 235 36 477 422 92 74 89 424 46 90 42 44 239 45 115 318 150 119 513 506 4 180 248 194 165 497 498 12 118 309 142 16 110 0\n540 -69 24 -16 0 242 410 411 412 404 405 431 406 237 233 538 539 5 504 436 340 13 443 365 239 115 150 119 323 173 220 183 118 309 142 16 110 0\n541 -68 -96 -16 0 228 233 410 411 412 237 404 405 431 406 401 402 403 226 538 472 539 5 473 457 4 180 194 174 191 163 504 436 340 13 443 365 239 115 150 97 137 107 275 30 62 34 117 292 154 6 98 0\n542 -177 105 126 32 -16 0 236 225 426 242 401 402 403 226 410 411 412 404 405 431 406 237 233 241 234 432 230 240 30 64 37 540 32 538 539 5 504 436 340 13 443 365 239 115 150 119 323 472 473 457 4 180 194 165 173 220 183 201 177 248 304 97 126 101 243 82 40 142 157 110 104 16 174 205 214 159 487 541 9 181 198 169 12 45 317 91 11 31 0\n543 75 90 105 126 25 -16 0 236 426 225 234 242 401 402 403 410 411 412 404 405 431 406 222 240 433 30 64 37 540 32 538 539 5 504 436 340 13 443 365 239 115 125 95 472 473 457 4 268 180 216 161 173 201 177 304 97 126 101 243 82 40 487 12 45 317 91 31 11 104 121 133 93 111 1 3 252 0\n544 105 126 25 32 -16 0 430 228 233 426 226 242 401 402 403 222 410 411 412 404 405 431 406 432 230 234 237 30 64 37 538 539 5 504 436 340 13 443 365 239 115 150 119 125 95 472 473 457 4 268 323 180 173 220 215 160 216 161 194 165 183 201 248 97 137 107 275 62 34 61 33 542 153 117 9 181 198 169 543 159 199 206 203 175 174 3 16 111 258 291 143 476 94 0\n545 126 25 32 -16 0 242 410 411 412 404 405 431 406 237 234 538 539 5 504 436 340 13 443 365 239 115 150 119 323 173 220 183 30 64 37 544 182 308 205 16 174 0\n546 -24 -16 0 430 228 233 410 411 412 242 404 405 431 406 401 402 403 221 429 538 472 539 5 473 457 4 180 436 340 13 173 220 215 160 97 137 107 275 30 62 34 61 33 37 265 52 58 21 25 476 0\n547 -96 3 32 -16 0 236 225 426 401 402 403 226 410 411 412 404 405 431 406 222 234 432 230 433 240 546 540 538 539 5 504 436 340 13 443 365 239 115 125 472 473 457 4 180 194 165 173 201 177 248 304 97 126 101 243 30 82 40 174 541 205 9 182 214 181 283 159 198 487 1 169 12 93 45 317 121 91 104 31 11 0\n548 -60 32 -16 0 430 228 233 426 226 410 411 412 242 404 405 431 406 401 402 403 222 432 538 472 539 5 473 457 4 180 436 340 13 173 220 215 160 194 165 248 97 137 107 275 30 62 34 61 33 110 263 124 141 94 117 476 9 291 0\n549 32 -16 0 236 242 410 411 412 404 405 431 406 237 221 546 538 539 5 504 436 340 13 443 365 239 115 150 119 323 173 220 183 30 82 548 16 547 20 51 78 545 38 0\n550 -96 -16 0 233 401 402 403 226 404 405 431 406 228 234 427 236 549 44 68 539 5 284 538 472 473 457 4 180 194 97 137 107 275 30 62 34 174 482 205 25 182 214 49 159 79 543 38 0\n551 -16 0 430 406 431 405 404 233 412 411 410 403 402 401 242 237 228 222 427 236 234 30 436 61 62 33 34 538 472 539 5 97 275 504 473 340 137 457 13 107 4 173 443 180 220 365 183 215 239 160 115 323 150 119 546 549 44 284 68 550 16 110 263 308 124 94 476 25 49 79 38 543 159 251 199 2 170 0\n552 -66 -67 -9 -52 23 0 412 411 410 450 512 379 13 451 382 0\n553 -59 -102 -67 -9 -52 0 439 351 353 352 0\n554 -9 27 -52 103 -118 25 -32 0 240 236 237 403 402 401 241 415 414 413 223 412 411 410 234 103 146 113 44 81 83 42 89 57 36 39 392 455 454 4 116 152 95 552 18 179 269 300 188 161 553 525 13 527 173 177 201 0\n555 -45 -52 0 434 335 0\n556 103 -9 -118 25 -32 0 240 236 428 551 403 402 401 415 414 413 418 421 231 392 455 454 44 81 83 42 89 57 36 554 4 306 552 235 18 553 0\n557 -102 192 318 -9 -10 -32 0 236 240 428 551 229 418 421 231 103 132 44 89 25 57 36 81 39 363 443 235 109 285 139 537 112 0\n558 -9 -10 25 -32 0 240 236 428 551 237 226 242 222 412 411 410 234 44 25 81 83 42 89 57 36 39 418 421 231 103 437 146 113 556 180 367 194 216 161 557 239 115 344 268 125 342 95 13 480 173 306 511 201 177 0\n559 -10 25 -32 0 240 406 431 405 404 412 411 410 409 551 408 407 44 89 25 57 36 558 5 520 555 13 10 355 440 0\n560 -45 20 56 92 25 -32 -60 0 240 237 426 225 409 551 408 407 403 402 401 238 242 222 228 232 433 296 559 6 98 145 112 517 131 116 44 89 26 110 124 94 97 243 456 520 555 126 454 10 101 4 167 438 449 180 385 263 376 209 348 216 452 448 177 235 161 239 36 307 287 115 268 302 73 125 40 95 480 475 7 489 476 39 33 250 66 69 31 20 11 1 104 159 133 206 111 175 3 0\n561 -23 -76 -103 132 25 0 242 238 222 180 160 207 210 179 216 161 36 74 42 239 115 268 125 475 95 0\n562 20 56 92 25 -32 -60 0 222 225 431 428 427 232 551 403 402 401 242 238 412 411 410 559 44 110 124 94 517 131 116 560 227 24 418 48 70 421 69 75 231 33 437 392 455 454 4 180 263 216 476 160 207 186 210 173 179 561 13 342 503 344 239 0\n563 -20 0 232 406 431 405 404 409 551 408 407 34 70 24 5 555 276 10 0\n564 -56 0 229 233 409 551 408 407 431 107 132 137 103 97 10 227 274 0\n565 -52 -92 0 404 405 431 406 273 555 5 0\n566 -92 0 230 551 171 195 167 231 565 0\n567 -117 -32 -60 0 222 236 225 427 232 563 566 564 403 402 401 412 411 410 242 562 38 77 81 25 517 131 116 79 21 110 124 94 48 70 69 72 33 36 476 160 267 262 4 13 180 173 215 220 0\n568 -53 3 149 49 85 -25 0 433 104 255 121 1 93 0\n569 -32 -60 0 433 222 232 242 238 401 402 403 407 408 551 409 225 426 404 405 431 406 564 566 563 236 427 430 562 38 65 77 31 81 25 517 131 116 567 24 5 97 243 456 520 555 126 454 10 101 4 167 438 449 180 385 376 209 348 216 452 448 177 235 239 36 307 115 73 125 40 78 20 568 11 168 253 185 1 159 0\n570 111 -25 0 430 427 406 431 405 404 426 225 409 551 408 407 238 403 402 401 232 242 222 433 38 65 31 20 48 24 5 97 243 456 520 555 126 454 10 101 167 438 397 209 348 458 177 235 457 36 441 307 347 4 73 357 349 180 40 239 216 115 125 568 11 168 253 185 1 159 0\n571 -25 -60 0 222 427 236 232 563 566 564 412 411 410 223 242 403 402 401 431 428 409 551 408 407 110 124 94 38 77 79 81 21 25 570 69 33 71 476 36 160 267 262 13 522 187 173 220 202 215 179 180 239 4 450 380 227 418 552 421 10 0\n572 -67 -95 -9 -60 34 70 0 233 428 551 234 242 415 414 413 173 220 201 15 418 421 231 392 455 454 519 569 110 142 118 552 516 18 182 179 212 0\n573 -95 -9 19 -60 34 70 0 222 428 551 229 242 403 402 401 426 226 432 563 566 564 110 418 421 231 103 132 141 117 392 455 454 569 124 94 173 220 572 4 180 248 263 194 215 165 160 9 476 291 0\n574 -59 102 -9 0 428 551 418 421 231 437 342 503 344 239 0\n575 -30 -105 27 99 63 126 0 42 474 67 31 0\n576 -103 95 -9 -111 -60 0 233 221 237 428 551 229 426 226 242 432 563 566 564 238 232 222 110 418 421 231 103 132 141 117 146 113 69 33 51 32 571 569 142 118 124 94 180 248 263 194 216 165 161 497 498 9 291 476 160 207 175 210 179 574 235 36 305 261 561 73 76 40 45 12 575 239 115 268 125 3 95 0\n577 -9 -111 -60 34 70 106 0 222 428 232 551 229 403 402 401 426 225 432 242 563 564 566 238 69 33 569 110 124 94 17 24 418 70 421 231 103 392 132 455 141 454 117 573 576 4 116 249 467 131 100 9 181 291 218 6 164 163 208 176 211 179 574 235 36 521 289 72 239 39 115 297 7 130 99 0\n578 -111 -60 34 70 106 0 233 232 406 431 405 404 409 551 408 407 403 402 401 240 242 563 566 564 222 571 110 124 94 142 69 33 577 5 97 456 520 555 153 454 10 117 438 397 348 458 235 457 36 441 347 4 92 357 349 180 263 485 239 216 476 115 268 161 125 475 95 0\n579 -60 34 70 106 0 233 427 406 431 405 404 426 225 409 551 408 407 238 403 402 401 232 240 242 222 563 566 564 433 110 124 142 94 571 578 20 48 24 5 97 243 456 520 555 126 153 454 10 101 117 167 438 397 209 348 458 177 235 457 36 441 307 347 4 73 92 357 349 180 263 40 485 239 216 115 268 161 125 95 475 476 250 1 159 206 185 175 168 3 111 254 133 11 104 0\n580 -75 25 41 185 5 157 207 63 27 0 161 177 159 206 185 175 168 3 111 254 133 11 104 0\n581 -96 10 192 178 48 200 0 432 563 564 566 165 174 482 204 191 181 163 9 6 117 98 154 0\n582 10 19 76 178 -103 200 34 70 106 0 426 226 221 563 566 564 180 194 248 579 581 16 37 265 52 476 21 0\n583 111 -88 -23 34 70 106 0 232 230 238 225 426 237 222 226 428 404 405 431 406 401 402 403 242 433 429 432 14 472 421 418 5 397 458 457 4 180 216 161 194 165 441 357 438 347 349 239 115 125 95 150 248 268 97 126 101 243 167 209 195 307 36 73 40 579 20 570 475 580 1 250 582 25 559 58 37 16 174 292 204 9 181 0\n584 -88 -23 34 70 106 0 230 428 406 431 405 404 403 402 401 426 222 237 226 242 232 429 432 36 73 14 472 441 579 167 421 438 195 418 5 357 397 347 458 349 457 239 4 115 268 180 248 125 150 194 216 95 165 161 583 69 78 33 38 475 582 25 559 58 37 16 174 292 204 9 181 0\n585 -10 -103 -23 34 70 106 0 241 426 226 240 566 431 232 564 551 237 429 415 414 413 432 230 584 231 103 146 579 555 227 24 70 36 92 180 194 493 248 165 497 56 32 500 496 498 12 118 149 115 157 104 113 305 73 40 25 58 37 74 16 42 292 18 9 179 313 181 211 11 196 168 0\n586 -102 62 98 -69 32 192 48 26 63 99 27 0 230 432 241 118 157 104 165 179 313 193 11 164 168 196 211 181 9 117 298 155 7 99 0\n587 -46 66 -69 32 -103 -117 63 99 -23 0 232 426 226 242 237 180 216 161 194 248 36 73 80 39 40 98 287 145 112 586 239 42 270 494 0\n588 -103 -23 34 70 106 0 240 237 429 551 431 232 426 226 242 563 564 566 238 36 73 584 231 555 227 24 80 39 56 32 70 579 500 103 146 113 305 496 40 92 180 248 194 216 165 493 161 497 498 12 118 149 115 585 587 6 163 289 208 176 586 239 42 270 494 0\n589 32 30 -67 25 26 105 -9 171 99 33 27 0 426 225 241 415 414 413 223 230 432 116 152 95 131 100 249 113 526 118 157 149 104 115 18 179 269 313 188 478 479 11 161 168 525 480 196 7 211 298 181 9 0\n590 -23 34 70 106 0 551 431 427 232 403 402 401 241 563 566 564 237 415 414 413 223 579 14 36 472 73 40 584 231 103 555 496 305 146 227 24 500 48 70 80 69 78 39 33 38 588 4 116 521 152 95 589 44 559 75 37 16 174 264 187 160 476 94 259 143 111 147 115 18 179 269 188 3 161 0\n591 -45 -102 23 0 551 412 411 410 520 365 13 443 0\n592 -41 -102 103 0 241 403 402 401 95 271 152 4 116 0\n593 -25 -95 4 76 19 0 427 563 566 564 236 38 260 77 476 81 25 0\n594 -102 -32 103 34 70 106 0 431 428 427 232 551 223 403 402 401 412 411 410 563 566 564 226 237 44 590 579 179 188 161 591 227 24 418 48 70 421 69 75 231 33 37 392 592 16 455 174 294 454 187 4 160 269 553 264 13 173 593 559 6 476 163 94 189 143 200 111 175 3 0\n595 -30 23 0 431 551 522 520 503 227 0\n596 -59 102 0 551 431 520 574 227 0\n597 102 103 23 0 415 414 413 403 402 401 431 428 409 551 408 407 595 18 450 596 472 4 380 227 418 552 421 10 0\n598 25 103 34 70 106 0 427 232 223 241 234 410 411 412 238 230 432 225 428 551 431 401 402 403 426 236 226 563 566 564 237 590 597 591 227 418 421 231 392 455 454 4 249 116 131 100 594 179 103 146 113 213 579 500 516 313 553 13 306 173 201 177 118 157 104 11 168 196 211 181 9 188 186 160 269 496 24 48 69 33 161 592 595 589 39 288 81 25 6 163 295 189 16 200 264 175 476 3 94 111 143 0\n599 103 34 70 106 0 223 431 428 427 232 551 403 402 401 412 411 410 236 590 597 179 591 188 227 24 418 48 421 69 231 33 392 455 454 4 553 13 173 186 160 598 38 593 79 21 0\n600 -25 76 -95 19 0 236 38 593 79 21 0\n601 32 69 33 105 -9 -103 0 426 226 429 24 56 32 180 194 165 248 497 498 12 0\n602 -95 -9 34 70 106 0 226 242 427 232 428 551 237 415 414 413 563 566 564 418 421 231 103 146 599 367 579 496 24 48 69 33 70 500 180 216 194 590 595 173 443 186 363 160 18 115 149 118 600 601 44 559 482 75 16 37 0\n603 -9 34 70 106 0 226 428 232 551 241 563 566 564 599 180 194 590 579 24 418 500 70 421 231 103 496 367 602 235 109 574 158 156 118 601 44 557 75 482 37 16 0\n604 34 70 106 0 407 408 551 409 410 411 412 404 405 431 406 590 603 5 520 555 13 10 355 440 0\n605 -45 -34 0 236 240 551 412 411 410 415 414 413 46 92 36 85 42 520 591 13 18 323 0\n606 -32 5 76 41 77 -95 -9 0 428 551 234 427 232 240 226 237 563 566 564 24 48 69 33 600 480 525 173 201 177 418 421 231 306 103 146 113 44 559 89 527 288 6 163 189 200 175 3 111 258 143 476 94 0\n607 -61 10 76 -95 19 0 237 563 566 564 111 258 143 476 94 0\n608 -46 -95 -34 0 234 426 427 232 225 401 402 403 428 551 236 223 431 237 240 230 432 605 227 46 85 42 323 239 179 188 161 418 421 231 387 453 452 384 592 173 186 160 392 455 454 4 269 606 116 131 100 24 48 69 33 600 480 525 249 201 212 182 177 306 103 146 113 98 288 145 589 112 45 315 91 31 478 11 7 168 298 196 9 211 181 0\n609 10 46 5 76 41 77 -95 19 0 563 564 566 226 600 173 607 6 3 163 175 190 192 0\n610 -95 -34 0 427 232 237 428 551 431 234 223 403 402 401 426 225 236 240 230 432 605 227 418 421 231 392 455 454 103 146 113 24 48 69 33 46 85 42 173 387 306 323 201 453 239 177 179 452 188 212 384 161 186 182 4 592 160 116 249 269 600 131 525 480 100 606 608 609 25 286 81 39 589 45 315 91 31 478 11 7 168 298 196 9 211 181 0\n611 -34 0 240 431 46 92 36 605 227 610 235 574 321 0\n612 -23 -70 0 241 232 415 414 413 429 431 428 551 237 403 402 401 119 158 109 472 150 115 36 441 319 73 18 40 42 357 59 84 227 45 24 418 55 87 421 31 44 231 103 305 521 146 4 113 474 461 601 0\n613 -26 -70 0 223 427 232 428 551 431 410 411 412 401 402 403 241 237 236 119 150 115 612 595 239 158 109 472 13 443 591 227 363 418 421 231 367 4 269 592 24 48 69 33 173 179 188 186 160 161 39 288 81 609 25 0\n614 -70 0 241 412 411 410 234 223 431 428 427 232 551 237 403 402 401 426 225 240 230 432 119 150 158 115 109 472 612 595 13 239 173 443 179 591 201 188 212 227 177 161 186 182 24 418 363 160 48 421 69 231 33 103 306 367 600 146 4 592 113 116 249 269 480 131 606 525 100 613 589 45 315 91 31 478 479 11 7 168 298 196 9 211 181 0\n615 106 0 614 611 604 0\n616 214 0 615 183 0\n617 -210 0 616 238 213 0\n618 -203 0 616 242 220 0\n619 -102 0 617 179 0\n620 -95 0 618 173 0\n621 -59 0 619 596 0\n622 23 0 620 621 235 0\n623 -31 0 621 472 0\n624 131 0 622 36 0\n625 302 0 622 441 0\n626 -66 0 622 615 318 0\n627 -135 0 624 232 73 0\n628 30 0 626 413 414 619 415 18 0\n629 -27 0 627 40 0\n630 138 0 628 42 0\n631 -45 0 628 625 357 0\n632 -119 0 630 429 59 0\n633 -141 0 630 627 84 0\n634 9 0 631 431 227 0\n635 -33 0 633 45 0\n636 117 0 634 24 0\n637 218 0 634 428 418 0\n638 -125 0 636 632 55 0\n639 -140 0 636 633 87 0\n640 -88 0 637 421 0\n641 -17 0 638 31 0\n642 -32 0 639 44 0\n643 52 0 640 551 231 0\n644 160 0 643 103 0\n645 -99 0 643 622 305 0\n646 -67 0 643 622 628 634 521 0\n647 -171 0 644 237 146 0\n648 103 0 646 401 402 403 623 4 0\n649 -63 0 647 113 0\n650 -105 0 649 641 629 645 628 474 0\n651 -69 0 649 641 645 629 628 461 0\n652 0 651 650 635 648 634 642 601 0\n"

theorem raw_n6_root (word : Fin 6 → Fin 3) :
    ClauseProof (fun val => ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val ∧ True) Sat.Clause.nil := by
  intro val hh
  have h := hh.left
  have bad := cert_n6_root (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 173) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 182) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 191) (val 192) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 201) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 210) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 219) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 228) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 237) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 246) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 255) (val 256) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 265) (val 266) (val 267) (val 268) (val 269) (val 270) (val 271) (val 272) (val 273) (val 274) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 283) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 292) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 301) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 310) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 319) (val 320) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 329) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 336) (val 337) (val 338) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 347) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 356) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 365) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 374) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 383) (val 384) (val 385) (val 386) (val 387) (val 388) (val 389) (val 390)
  exact Or.elim (bad)
    (fun badL0 => Or.elim (badL0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c0 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c1 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => input_n6_c2 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2.1) (badR8.2.2.2.2.1) (badR8.2.2.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c3 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c4 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => input_n6_c5 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2.1) (badR8.2.2.2.2.1) (badR8.2.2.2.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c6 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c7 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c8 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2.1) (badR8.2.2.2.2.1) (badR8.2.2.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c9 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c10 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => input_n6_c11 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2.1) (badR8.2.2.2.2.1) (badR8.2.2.2.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c12 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c13 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c14 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c15 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2.1) (badL7.2.2.2.2.1) (badL7.2.2.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c16 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c17 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2.1) (badR8.2.2.2.2.1) (badR8.2.2.2.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c18 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c19 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c20 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c21 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c22 word val h (badR8.1) (badR8.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c23 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c24 word val h (badR8.1) (badR8.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c25 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c26 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c27 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c28 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c29 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c30 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c31 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c32 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c33 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c34 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c35 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c36 word val h (badR8.1) (badR8.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c37 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c38 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c39 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c40 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c41 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c42 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c43 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c44 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c45 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c46 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c47 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c48 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c49 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c50 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c51 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c52 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c53 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c54 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c55 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c56 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c57 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c58 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c59 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c60 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c61 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c62 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c63 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c64 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c65 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c66 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c67 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c68 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c69 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c70 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c71 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c72 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c73 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c74 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c75 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c76 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c77 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c78 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c79 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c80 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c81 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c82 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c83 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c84 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c85 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c86 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c87 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c88 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c89 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c90 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c91 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c92 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c93 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c94 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c95 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c96 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c97 word val h (badR8.1) (badR8.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c98 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c99 word val h (badR8.1) (badR8.2)))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c100 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c101 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c102 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c103 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c104 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c105 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c106 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c107 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c108 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c109 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c110 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c111 word val h (badR8.1) (badR8.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c112 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c113 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c114 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c115 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c116 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c117 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c118 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c119 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c120 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c121 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c122 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c123 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c124 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c125 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c126 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c127 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c128 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c129 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c130 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c131 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c132 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c133 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c134 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c135 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c136 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c137 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c138 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c139 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c140 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c141 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c142 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c143 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c144 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c145 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c146 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c147 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c148 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c149 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c150 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c151 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c152 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c153 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c154 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c155 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c156 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c157 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c158 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c159 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c160 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c161 word val h (badR8.1) (badR8.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c162 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c163 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c164 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c165 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c166 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c167 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c168 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c169 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c170 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c171 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c172 word val h (badR8.1) (badR8.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c173 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c174 word val h (badR8.1) (badR8.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c175 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c176 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c177 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c178 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c179 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c180 word val h (badR8.1) (badR8.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c181 word val h (badL7.1) (badL7.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c182 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c183 word val h (badR8.1) (badR8.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c184 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c185 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c186 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c187 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c188 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c189 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c190 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c191 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c192 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c193 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c194 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c195 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c196 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c197 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c198 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c199 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))))
    (fun badR0 => Or.elim (badR0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c200 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c201 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c202 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c203 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c204 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c205 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c206 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c207 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c208 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c209 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c210 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c211 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c212 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c213 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c214 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c215 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c216 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c217 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c218 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c219 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c220 word val h (badR8))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c221 word val h (badL8))
    (fun badR8 => input_n6_c222 word val h (badR8)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c223 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c224 word val h (badR8)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c225 word val h (badL7))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c226 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c227 word val h (badR8))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c228 word val h (badL7))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c229 word val h (badL8))
    (fun badR8 => input_n6_c230 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c231 word val h (badL7))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c232 word val h (badL8))
    (fun badR8 => input_n6_c233 word val h (badR8))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c234 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c235 word val h (badL8))
    (fun badR8 => input_n6_c236 word val h (badR8))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c237 word val h (badL7))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c238 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c239 word val h (badR8))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c240 word val h (badL7))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c241 word val h (badL8))
    (fun badR8 => input_n6_c242 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c243 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c244 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c245 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c246 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c247 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c248 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c249 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c250 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c251 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c252 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c253 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c254 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c255 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c256 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c257 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c258 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c259 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c260 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c261 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c262 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c263 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c264 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c265 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c266 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c267 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c268 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c269 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c270 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c271 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c272 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c273 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c274 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c275 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c276 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c277 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c278 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c279 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c280 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c281 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c282 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c283 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c284 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c285 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c286 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c287 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c288 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c289 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c290 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c291 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c292 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c293 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c294 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c295 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c296 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c297 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c298 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c299 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c300 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c301 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c302 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c303 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c304 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c305 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c306 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c307 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c308 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c309 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c310 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c311 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c312 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c313 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c314 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c315 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c316 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c317 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c318 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c319 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c320 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c321 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c322 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c323 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c324 word val h (badR8.1) (badR8.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c325 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c326 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c327 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c328 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c329 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c330 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c331 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c332 word val h (badL8.1) (badL8.2))
    (fun badR8 => input_n6_c333 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c334 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c335 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c336 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c337 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c338 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c339 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c340 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c341 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c342 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c343 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c344 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c345 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c346 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c347 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c348 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c349 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c350 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c351 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c352 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c353 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c354 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c355 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c356 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c357 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c358 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c359 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c360 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c361 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c362 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c363 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c364 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c365 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c366 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c367 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c368 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c369 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c370 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c371 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c372 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c373 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c374 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c375 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c376 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c377 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c378 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c379 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c380 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c381 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c382 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c383 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c384 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c385 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c386 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c387 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c388 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c389 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => input_n6_c390 word val h (badL7.1) (badL7.2.1) (badL7.2.2.1) (badL7.2.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c391 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c392 word val h (badR8.1) (badR8.2.1) (badR8.2.2)))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => input_n6_c393 word val h (badL7.1) (badL7.2.1) (badL7.2.2))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c394 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => input_n6_c395 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n6_c396 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c397 word val h (badR8.1) (badR8.2.1) (badR8.2.2.1) (badR8.2.2.2)))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n6_c398 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => input_n6_c399 word val h (badR8.1) (badR8.2.1) (badR8.2.2))))))))))

theorem exclude_n6_root (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) (_hp : True) : False :=
  raw_n6_root word val ⟨h, True.intro⟩

theorem universal_n6_root (word : Fin 6 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 6) lexPerm val) : False :=
  raw_n6_root word val ⟨h, True.intro⟩
end OPG1808SmallOrders


-- Bundled whole source: LeafN7Root.lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OPG1808SmallOrders
open ModuleOPG1808Certificate OrdinaryLRATBridge

theorem input_n7_c0 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 2, Sat.Literal.pos 14, Sat.Literal.pos 51, Sat.Literal.pos 63, Sat.Literal.pos 100, Sat.Literal.pos 112] :=
  h.toModel.orientation_clause (0 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c1 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 51] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c2 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 63] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c3 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 100] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c4 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 112] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c5 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 3, Sat.Literal.pos 21, Sat.Literal.pos 52, Sat.Literal.pos 70, Sat.Literal.pos 101, Sat.Literal.pos 119] :=
  h.toModel.orientation_clause (0 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c6 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 101] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c7 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 70] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c8 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 101] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c9 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 119] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c10 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 4, Sat.Literal.pos 28, Sat.Literal.pos 53, Sat.Literal.pos 77, Sat.Literal.pos 102, Sat.Literal.pos 126] :=
  h.toModel.orientation_clause (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c11 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 53] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c12 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 77] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c13 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 102] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c14 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 126] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c15 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.neg 53] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c16 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.neg 102] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c17 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 77] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c18 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 102] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c19 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 126] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c20 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 77, Sat.Literal.neg 126] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c21 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 5, Sat.Literal.pos 35, Sat.Literal.pos 54, Sat.Literal.pos 84, Sat.Literal.pos 103, Sat.Literal.pos 133] :=
  h.toModel.orientation_clause (0 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c22 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.neg 35] :=
  h.toModel.opposites_clause (0 : Fin 3) (0 : Fin 3) (0 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c23 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.neg 84] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c24 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.neg 133] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c25 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 35, Sat.Literal.neg 54] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c26 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 35, Sat.Literal.neg 84] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c27 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 35, Sat.Literal.neg 133] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (5 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c28 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 84, Sat.Literal.neg 103] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (5 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c29 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 103, Sat.Literal.neg 133] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (0 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c30 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 6, Sat.Literal.pos 42, Sat.Literal.pos 55, Sat.Literal.pos 91, Sat.Literal.pos 104, Sat.Literal.pos 140] :=
  h.toModel.orientation_clause (0 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c31 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 42, Sat.Literal.neg 140] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c32 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 91, Sat.Literal.neg 140] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (by decide)

theorem input_n7_c33 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 9, Sat.Literal.pos 15, Sat.Literal.pos 58, Sat.Literal.pos 64, Sat.Literal.pos 107, Sat.Literal.pos 113] :=
  h.toModel.orientation_clause (1 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c34 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 10, Sat.Literal.pos 22, Sat.Literal.pos 59, Sat.Literal.pos 71, Sat.Literal.pos 108, Sat.Literal.pos 120] :=
  h.toModel.orientation_clause (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c35 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 59] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c36 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 108] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c37 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 71] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c38 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 108] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c39 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 120] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c40 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 11, Sat.Literal.pos 29, Sat.Literal.pos 60, Sat.Literal.pos 78, Sat.Literal.pos 109, Sat.Literal.pos 127] :=
  h.toModel.orientation_clause (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c41 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 29] :=
  h.toModel.opposites_clause (0 : Fin 3) (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c42 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 60] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c43 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 78] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c44 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 109] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c45 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 127] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c46 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.neg 60] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c47 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.neg 109] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c48 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 78] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c49 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 109] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c50 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 127] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c51 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 78, Sat.Literal.neg 109] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c52 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 127] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c53 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 12, Sat.Literal.pos 36, Sat.Literal.pos 61, Sat.Literal.pos 85, Sat.Literal.pos 110, Sat.Literal.pos 134] :=
  h.toModel.orientation_clause (1 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c54 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.neg 36] :=
  h.toModel.opposites_clause (0 : Fin 3) (0 : Fin 3) (1 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c55 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.neg 110] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c56 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.neg 134] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c57 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.neg 61] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c58 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.neg 85] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c59 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.neg 110] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (5 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c60 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.neg 134] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (5 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c61 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.neg 110] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c62 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 13, Sat.Literal.pos 43, Sat.Literal.pos 62, Sat.Literal.pos 92, Sat.Literal.pos 111, Sat.Literal.pos 141] :=
  h.toModel.orientation_clause (1 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c63 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 43, Sat.Literal.neg 92] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (6 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c64 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 43, Sat.Literal.neg 141] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (1 : Fin 7) (by decide)

theorem input_n7_c65 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 17, Sat.Literal.pos 23, Sat.Literal.pos 66, Sat.Literal.pos 72, Sat.Literal.pos 115, Sat.Literal.pos 121] :=
  h.toModel.orientation_clause (2 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c66 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 66] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c67 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 115] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c68 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 18, Sat.Literal.pos 30, Sat.Literal.pos 67, Sat.Literal.pos 79, Sat.Literal.pos 116, Sat.Literal.pos 128] :=
  h.toModel.orientation_clause (2 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c69 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 67] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c70 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 116] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c71 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 128] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c72 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 30, Sat.Literal.neg 67] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c73 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 30, Sat.Literal.neg 116] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c74 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 128] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c75 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 19, Sat.Literal.pos 37, Sat.Literal.pos 68, Sat.Literal.pos 86, Sat.Literal.pos 117, Sat.Literal.pos 135] :=
  h.toModel.orientation_clause (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c76 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 37] :=
  h.toModel.opposites_clause (0 : Fin 3) (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c77 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 68] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c78 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 135] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c79 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 37, Sat.Literal.neg 68] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c80 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 37, Sat.Literal.neg 117] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (5 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c81 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.neg 86] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c82 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.neg 117] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c83 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.neg 135] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c84 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 135] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c85 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 20, Sat.Literal.pos 44, Sat.Literal.pos 69, Sat.Literal.pos 93, Sat.Literal.pos 118, Sat.Literal.pos 142] :=
  h.toModel.orientation_clause (2 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c86 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 20, Sat.Literal.neg 69] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c87 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 69] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (6 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c88 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.neg 142] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c89 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 69, Sat.Literal.neg 93] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (2 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c90 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 69, Sat.Literal.neg 118] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c91 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 93, Sat.Literal.neg 118] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c92 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 93, Sat.Literal.neg 142] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (2 : Fin 7) (by decide)

theorem input_n7_c93 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 118, Sat.Literal.neg 142] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (2 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c94 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 25, Sat.Literal.pos 31, Sat.Literal.pos 74, Sat.Literal.pos 80, Sat.Literal.pos 123, Sat.Literal.pos 129] :=
  h.toModel.orientation_clause (3 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c95 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 74] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c96 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 123] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c97 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 123] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c98 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 26, Sat.Literal.pos 38, Sat.Literal.pos 75, Sat.Literal.pos 87, Sat.Literal.pos 124, Sat.Literal.pos 136] :=
  h.toModel.orientation_clause (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c99 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 38] :=
  h.toModel.opposites_clause (0 : Fin 3) (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c100 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 75] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c101 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 124] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c102 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.neg 75] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (5 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c103 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 87] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c104 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 124] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c105 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 136] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c106 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 27, Sat.Literal.pos 45, Sat.Literal.pos 76, Sat.Literal.pos 94, Sat.Literal.pos 125, Sat.Literal.pos 143] :=
  h.toModel.orientation_clause (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c107 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 27, Sat.Literal.neg 94] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c108 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 27, Sat.Literal.neg 143] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c109 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 76] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (6 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c110 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 125] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c111 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.neg 143] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c112 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.neg 94] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c113 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.neg 143] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c114 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.neg 125] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c115 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.neg 143] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (by decide)

theorem input_n7_c116 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 125, Sat.Literal.neg 143] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (3 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c117 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 33, Sat.Literal.pos 39, Sat.Literal.pos 82, Sat.Literal.pos 88, Sat.Literal.pos 131, Sat.Literal.pos 137] :=
  h.toModel.orientation_clause (4 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c118 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 82] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c119 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 131] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c120 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 131] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (by decide)

theorem input_n7_c121 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 34, Sat.Literal.pos 46, Sat.Literal.pos 83, Sat.Literal.pos 95, Sat.Literal.pos 132, Sat.Literal.pos 144] :=
  h.toModel.orientation_clause (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c122 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34, Sat.Literal.neg 83] :=
  h.toModel.colors_clause (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c123 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34, Sat.Literal.neg 132] :=
  h.toModel.colors_clause (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c124 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.neg 83] :=
  h.toModel.opposites_clause (0 : Fin 3) (1 : Fin 3) (6 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c125 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.neg 132] :=
  h.toModel.opposites_clause (0 : Fin 3) (2 : Fin 3) (6 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c126 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.neg 95] :=
  h.toModel.opposites_clause (1 : Fin 3) (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c127 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.neg 132] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c128 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.neg 144] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c129 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 95, Sat.Literal.neg 132] :=
  h.toModel.opposites_clause (1 : Fin 3) (2 : Fin 3) (6 : Fin 7) (4 : Fin 7) (by decide)

theorem input_n7_c130 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 132, Sat.Literal.neg 144] :=
  h.toModel.opposites_clause (2 : Fin 3) (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c131 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 41, Sat.Literal.pos 47, Sat.Literal.pos 90, Sat.Literal.pos 96, Sat.Literal.pos 139, Sat.Literal.pos 145] :=
  h.toModel.orientation_clause (5 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c132 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 90, Sat.Literal.neg 139] :=
  h.toModel.colors_clause (1 : Fin 3) (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (by decide)

theorem input_n7_c133 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.pos 148] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (1 : Fin 7)

theorem input_n7_c134 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.pos 149] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c135 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.pos 150] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c136 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.pos 151] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c137 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.pos 152] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (5 : Fin 7)

theorem input_n7_c138 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 6, Sat.Literal.pos 153] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (0 : Fin 7) (6 : Fin 7)

theorem input_n7_c139 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.pos 156] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c140 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.pos 157] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c141 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.pos 158] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c142 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.pos 159] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c143 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 13, Sat.Literal.pos 160] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (1 : Fin 7) (6 : Fin 7)

theorem input_n7_c144 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 14, Sat.Literal.pos 161] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (0 : Fin 7)

theorem input_n7_c145 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 15, Sat.Literal.pos 162] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (1 : Fin 7)

theorem input_n7_c146 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.pos 164] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c147 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.pos 165] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c148 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.pos 166] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c149 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 20, Sat.Literal.pos 167] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c150 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 21, Sat.Literal.pos 168] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c151 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 22, Sat.Literal.pos 169] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (1 : Fin 7)

theorem input_n7_c152 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 23, Sat.Literal.pos 170] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (2 : Fin 7)

theorem input_n7_c153 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.pos 172] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c154 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.pos 173] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c155 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 27, Sat.Literal.pos 174] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c156 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 28, Sat.Literal.pos 175] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c157 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 29, Sat.Literal.pos 176] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c158 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 30, Sat.Literal.pos 177] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c159 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 31, Sat.Literal.pos 178] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (3 : Fin 7)

theorem input_n7_c160 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.pos 180] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c161 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 34, Sat.Literal.pos 181] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c162 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 35, Sat.Literal.pos 182] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c163 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 36, Sat.Literal.pos 183] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c164 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 37, Sat.Literal.pos 184] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c165 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 38, Sat.Literal.pos 185] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c166 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 39, Sat.Literal.pos 186] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (4 : Fin 7)

theorem input_n7_c167 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 41, Sat.Literal.pos 188] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c168 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 42, Sat.Literal.pos 189] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c169 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 43, Sat.Literal.pos 190] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c170 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 44, Sat.Literal.pos 191] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c171 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 45, Sat.Literal.pos 192] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c172 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 46, Sat.Literal.pos 193] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c173 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 47, Sat.Literal.pos 194] :=
  h.toModel.arc_reach_clause (0 : Fin 3) (6 : Fin 7) (5 : Fin 7)

theorem input_n7_c174 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148, Sat.Literal.neg 156, Sat.Literal.pos 149] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c175 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148, Sat.Literal.neg 157, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c176 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148, Sat.Literal.neg 158, Sat.Literal.pos 151] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c177 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 148, Sat.Literal.neg 160, Sat.Literal.pos 153] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (1 : Fin 7) (6 : Fin 7)

theorem input_n7_c178 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 149, Sat.Literal.neg 164, Sat.Literal.pos 150] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c179 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 149, Sat.Literal.neg 165, Sat.Literal.pos 151] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c180 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 149, Sat.Literal.neg 167, Sat.Literal.pos 153] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c181 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150, Sat.Literal.neg 172, Sat.Literal.pos 151] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c182 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150, Sat.Literal.neg 173, Sat.Literal.pos 152] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c183 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 150, Sat.Literal.neg 174, Sat.Literal.pos 153] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c184 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 151, Sat.Literal.neg 181, Sat.Literal.pos 153] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c185 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 152, Sat.Literal.neg 188, Sat.Literal.pos 153] :=
  h.toModel.trans_clause (0 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c186 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 156, Sat.Literal.neg 164, Sat.Literal.pos 157] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c187 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 156, Sat.Literal.neg 165, Sat.Literal.pos 158] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c188 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 156, Sat.Literal.neg 166, Sat.Literal.pos 159] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c189 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 156, Sat.Literal.neg 167, Sat.Literal.pos 160] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c190 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 157, Sat.Literal.neg 172, Sat.Literal.pos 158] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c191 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 157, Sat.Literal.neg 173, Sat.Literal.pos 159] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c192 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 157, Sat.Literal.neg 174, Sat.Literal.pos 160] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c193 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 158, Sat.Literal.neg 175, Sat.Literal.pos 154] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c194 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 158, Sat.Literal.neg 180, Sat.Literal.pos 159] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c195 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 158, Sat.Literal.neg 181, Sat.Literal.pos 160] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c196 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 159, Sat.Literal.neg 182, Sat.Literal.pos 154] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c197 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 159, Sat.Literal.neg 188, Sat.Literal.pos 160] :=
  h.toModel.trans_clause (0 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c198 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 161, Sat.Literal.neg 148, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (0 : Fin 7) (1 : Fin 7)

theorem input_n7_c199 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164, Sat.Literal.neg 168, Sat.Literal.pos 161] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c200 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164, Sat.Literal.neg 169, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (1 : Fin 7)

theorem input_n7_c201 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164, Sat.Literal.neg 172, Sat.Literal.pos 165] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c202 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164, Sat.Literal.neg 173, Sat.Literal.pos 166] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c203 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 164, Sat.Literal.neg 174, Sat.Literal.pos 167] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c204 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 165, Sat.Literal.neg 175, Sat.Literal.pos 161] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c205 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 165, Sat.Literal.neg 176, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c206 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 165, Sat.Literal.neg 180, Sat.Literal.pos 166] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c207 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 165, Sat.Literal.neg 181, Sat.Literal.pos 167] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c208 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 182, Sat.Literal.pos 161] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c209 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 183, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c210 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 166, Sat.Literal.neg 188, Sat.Literal.pos 167] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c211 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 167, Sat.Literal.neg 190, Sat.Literal.pos 162] :=
  h.toModel.trans_clause (0 : Fin 3) (2 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c212 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 168, Sat.Literal.neg 149, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c213 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 169, Sat.Literal.neg 156, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c214 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 172, Sat.Literal.neg 175, Sat.Literal.pos 168] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c215 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 172, Sat.Literal.neg 176, Sat.Literal.pos 169] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c216 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 172, Sat.Literal.neg 177, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c217 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 172, Sat.Literal.neg 180, Sat.Literal.pos 173] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c218 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 172, Sat.Literal.neg 181, Sat.Literal.pos 174] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c219 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 182, Sat.Literal.pos 168] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c220 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 183, Sat.Literal.pos 169] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c221 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 184, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c222 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 173, Sat.Literal.neg 188, Sat.Literal.pos 174] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c223 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 174, Sat.Literal.neg 190, Sat.Literal.pos 169] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c224 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 174, Sat.Literal.neg 191, Sat.Literal.pos 170] :=
  h.toModel.trans_clause (0 : Fin 3) (3 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c225 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 148, Sat.Literal.pos 176] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (0 : Fin 7) (1 : Fin 7)

theorem input_n7_c226 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 149, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c227 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 175, Sat.Literal.neg 150, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c228 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 176, Sat.Literal.neg 156, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c229 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 176, Sat.Literal.neg 157, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c230 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 177, Sat.Literal.neg 164, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c231 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 180, Sat.Literal.neg 182, Sat.Literal.pos 175] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c232 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 180, Sat.Literal.neg 183, Sat.Literal.pos 176] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c233 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 180, Sat.Literal.neg 184, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c234 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 180, Sat.Literal.neg 185, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c235 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 180, Sat.Literal.neg 188, Sat.Literal.pos 181] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c236 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 181, Sat.Literal.neg 190, Sat.Literal.pos 176] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c237 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 181, Sat.Literal.neg 191, Sat.Literal.pos 177] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c238 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 181, Sat.Literal.neg 192, Sat.Literal.pos 178] :=
  h.toModel.trans_clause (0 : Fin 3) (4 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c239 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 182, Sat.Literal.neg 148, Sat.Literal.pos 183] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (0 : Fin 7) (1 : Fin 7)

theorem input_n7_c240 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 182, Sat.Literal.neg 149, Sat.Literal.pos 184] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c241 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 182, Sat.Literal.neg 150, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c242 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 182, Sat.Literal.neg 151, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c243 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 183, Sat.Literal.neg 156, Sat.Literal.pos 184] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c244 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 183, Sat.Literal.neg 157, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c245 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 183, Sat.Literal.neg 158, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c246 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 184, Sat.Literal.neg 164, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c247 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 184, Sat.Literal.neg 165, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c248 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 185, Sat.Literal.neg 172, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c249 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 188, Sat.Literal.neg 190, Sat.Literal.pos 183] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c250 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 188, Sat.Literal.neg 191, Sat.Literal.pos 184] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c251 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 188, Sat.Literal.neg 192, Sat.Literal.pos 185] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c252 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 188, Sat.Literal.neg 193, Sat.Literal.pos 186] :=
  h.toModel.trans_clause (0 : Fin 3) (5 : Fin 7) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c253 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 189, Sat.Literal.neg 148, Sat.Literal.pos 190] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (0 : Fin 7) (1 : Fin 7)

theorem input_n7_c254 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 156, Sat.Literal.pos 191] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c255 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 157, Sat.Literal.pos 192] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c256 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 158, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c257 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 190, Sat.Literal.neg 159, Sat.Literal.pos 194] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c258 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 191, Sat.Literal.neg 164, Sat.Literal.pos 192] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c259 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 191, Sat.Literal.neg 165, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c260 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 191, Sat.Literal.neg 166, Sat.Literal.pos 194] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c261 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 192, Sat.Literal.neg 172, Sat.Literal.pos 193] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c262 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 192, Sat.Literal.neg 173, Sat.Literal.pos 194] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c263 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 193, Sat.Literal.neg 180, Sat.Literal.pos 194] :=
  h.toModel.trans_clause (0 : Fin 3) (6 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c264 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.pos 198] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c265 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.pos 199] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c266 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.pos 200] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c267 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.pos 201] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 7) (5 : Fin 7)

theorem input_n7_c268 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 55, Sat.Literal.pos 202] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (0 : Fin 7) (6 : Fin 7)

theorem input_n7_c269 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.pos 205] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c270 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.pos 206] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c271 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.pos 207] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c272 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.pos 208] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c273 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 62, Sat.Literal.pos 209] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (1 : Fin 7) (6 : Fin 7)

theorem input_n7_c274 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 63, Sat.Literal.pos 210] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (0 : Fin 7)

theorem input_n7_c275 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 64, Sat.Literal.pos 211] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (1 : Fin 7)

theorem input_n7_c276 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.pos 213] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c277 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.pos 214] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c278 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.pos 215] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c279 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 69, Sat.Literal.pos 216] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c280 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 70, Sat.Literal.pos 217] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c281 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 71, Sat.Literal.pos 218] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (1 : Fin 7)

theorem input_n7_c282 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 72, Sat.Literal.pos 219] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (2 : Fin 7)

theorem input_n7_c283 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.pos 221] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c284 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.pos 222] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c285 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 76, Sat.Literal.pos 223] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c286 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 77, Sat.Literal.pos 224] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c287 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 78, Sat.Literal.pos 225] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c288 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 79, Sat.Literal.pos 226] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c289 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 80, Sat.Literal.pos 227] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (3 : Fin 7)

theorem input_n7_c290 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.pos 229] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c291 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 83, Sat.Literal.pos 230] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c292 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 84, Sat.Literal.pos 231] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c293 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 85, Sat.Literal.pos 232] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c294 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 86, Sat.Literal.pos 233] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c295 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 87, Sat.Literal.pos 234] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c296 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 88, Sat.Literal.pos 235] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (4 : Fin 7)

theorem input_n7_c297 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 90, Sat.Literal.pos 237] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c298 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 91, Sat.Literal.pos 238] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c299 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 92, Sat.Literal.pos 239] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c300 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 93, Sat.Literal.pos 240] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c301 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 94, Sat.Literal.pos 241] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c302 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 95, Sat.Literal.pos 242] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c303 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 96, Sat.Literal.pos 243] :=
  h.toModel.arc_reach_clause (1 : Fin 3) (6 : Fin 7) (5 : Fin 7)

theorem input_n7_c304 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 198, Sat.Literal.neg 215, Sat.Literal.pos 201] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c305 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 198, Sat.Literal.neg 216, Sat.Literal.pos 202] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c306 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 199, Sat.Literal.neg 221, Sat.Literal.pos 200] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c307 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 199, Sat.Literal.neg 222, Sat.Literal.pos 201] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c308 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 199, Sat.Literal.neg 223, Sat.Literal.pos 202] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c309 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 200, Sat.Literal.neg 229, Sat.Literal.pos 201] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c310 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 200, Sat.Literal.neg 230, Sat.Literal.pos 202] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c311 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 201, Sat.Literal.neg 237, Sat.Literal.pos 202] :=
  h.toModel.trans_clause (1 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c312 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 205, Sat.Literal.neg 210, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (0 : Fin 7)

theorem input_n7_c313 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 205, Sat.Literal.neg 214, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c314 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 205, Sat.Literal.neg 215, Sat.Literal.pos 208] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c315 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 206, Sat.Literal.neg 217, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c316 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 206, Sat.Literal.neg 221, Sat.Literal.pos 207] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c317 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 206, Sat.Literal.neg 222, Sat.Literal.pos 208] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c318 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 206, Sat.Literal.neg 223, Sat.Literal.pos 209] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c319 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 207, Sat.Literal.neg 224, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c320 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 207, Sat.Literal.neg 229, Sat.Literal.pos 208] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c321 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 207, Sat.Literal.neg 230, Sat.Literal.pos 209] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c322 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 208, Sat.Literal.neg 231, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c323 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 208, Sat.Literal.neg 237, Sat.Literal.pos 209] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c324 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 209, Sat.Literal.neg 238, Sat.Literal.pos 203] :=
  h.toModel.trans_clause (1 : Fin 3) (1 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c325 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 213, Sat.Literal.neg 218, Sat.Literal.pos 211] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (1 : Fin 7)

theorem input_n7_c326 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 213, Sat.Literal.neg 221, Sat.Literal.pos 214] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c327 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 213, Sat.Literal.neg 222, Sat.Literal.pos 215] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c328 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 213, Sat.Literal.neg 223, Sat.Literal.pos 216] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c329 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 214, Sat.Literal.neg 224, Sat.Literal.pos 210] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c330 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 214, Sat.Literal.neg 225, Sat.Literal.pos 211] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c331 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 214, Sat.Literal.neg 229, Sat.Literal.pos 215] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c332 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 214, Sat.Literal.neg 230, Sat.Literal.pos 216] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c333 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 215, Sat.Literal.neg 231, Sat.Literal.pos 210] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c334 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 215, Sat.Literal.neg 232, Sat.Literal.pos 211] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c335 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 215, Sat.Literal.neg 237, Sat.Literal.pos 216] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c336 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 216, Sat.Literal.neg 239, Sat.Literal.pos 211] :=
  h.toModel.trans_clause (1 : Fin 3) (2 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c337 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 217, Sat.Literal.neg 198, Sat.Literal.pos 219] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c338 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 218, Sat.Literal.neg 205, Sat.Literal.pos 219] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c339 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 221, Sat.Literal.neg 225, Sat.Literal.pos 218] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c340 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 221, Sat.Literal.neg 226, Sat.Literal.pos 219] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c341 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 221, Sat.Literal.neg 229, Sat.Literal.pos 222] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c342 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 221, Sat.Literal.neg 230, Sat.Literal.pos 223] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c343 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 222, Sat.Literal.neg 231, Sat.Literal.pos 217] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c344 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 222, Sat.Literal.neg 232, Sat.Literal.pos 218] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c345 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 222, Sat.Literal.neg 233, Sat.Literal.pos 219] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c346 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 222, Sat.Literal.neg 237, Sat.Literal.pos 223] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c347 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 223, Sat.Literal.neg 239, Sat.Literal.pos 218] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c348 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 223, Sat.Literal.neg 240, Sat.Literal.pos 219] :=
  h.toModel.trans_clause (1 : Fin 3) (3 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c349 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 224, Sat.Literal.neg 199, Sat.Literal.pos 227] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c350 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 225, Sat.Literal.neg 205, Sat.Literal.pos 226] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (1 : Fin 7) (2 : Fin 7)

theorem input_n7_c351 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 225, Sat.Literal.neg 206, Sat.Literal.pos 227] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c352 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 226, Sat.Literal.neg 213, Sat.Literal.pos 227] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c353 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 229, Sat.Literal.neg 231, Sat.Literal.pos 224] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c354 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 229, Sat.Literal.neg 232, Sat.Literal.pos 225] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c355 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 229, Sat.Literal.neg 233, Sat.Literal.pos 226] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c356 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 229, Sat.Literal.neg 234, Sat.Literal.pos 227] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c357 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 229, Sat.Literal.neg 237, Sat.Literal.pos 230] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c358 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 238, Sat.Literal.pos 224] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c359 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 239, Sat.Literal.pos 225] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c360 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 240, Sat.Literal.pos 226] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c361 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 230, Sat.Literal.neg 241, Sat.Literal.pos 227] :=
  h.toModel.trans_clause (1 : Fin 3) (4 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c362 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 231, Sat.Literal.neg 199, Sat.Literal.pos 234] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c363 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 231, Sat.Literal.neg 200, Sat.Literal.pos 235] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c364 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 232, Sat.Literal.neg 206, Sat.Literal.pos 234] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c365 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 232, Sat.Literal.neg 207, Sat.Literal.pos 235] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c366 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 233, Sat.Literal.neg 213, Sat.Literal.pos 234] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c367 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 233, Sat.Literal.neg 214, Sat.Literal.pos 235] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c368 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 234, Sat.Literal.neg 221, Sat.Literal.pos 235] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c369 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 237, Sat.Literal.neg 238, Sat.Literal.pos 231] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c370 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 237, Sat.Literal.neg 239, Sat.Literal.pos 232] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c371 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 237, Sat.Literal.neg 240, Sat.Literal.pos 233] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c372 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 237, Sat.Literal.neg 241, Sat.Literal.pos 234] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c373 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 237, Sat.Literal.neg 242, Sat.Literal.pos 235] :=
  h.toModel.trans_clause (1 : Fin 3) (5 : Fin 7) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c374 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 238, Sat.Literal.neg 199, Sat.Literal.pos 241] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c375 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 238, Sat.Literal.neg 200, Sat.Literal.pos 242] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c376 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 238, Sat.Literal.neg 201, Sat.Literal.pos 243] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (0 : Fin 7) (5 : Fin 7)

theorem input_n7_c377 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 239, Sat.Literal.neg 206, Sat.Literal.pos 241] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c378 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 239, Sat.Literal.neg 207, Sat.Literal.pos 242] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c379 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 239, Sat.Literal.neg 208, Sat.Literal.pos 243] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c380 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 240, Sat.Literal.neg 213, Sat.Literal.pos 241] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (2 : Fin 7) (3 : Fin 7)

theorem input_n7_c381 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 240, Sat.Literal.neg 214, Sat.Literal.pos 242] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c382 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 240, Sat.Literal.neg 215, Sat.Literal.pos 243] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c383 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 241, Sat.Literal.neg 221, Sat.Literal.pos 242] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c384 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 241, Sat.Literal.neg 222, Sat.Literal.pos 243] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c385 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 242, Sat.Literal.neg 229, Sat.Literal.pos 243] :=
  h.toModel.trans_clause (1 : Fin 3) (6 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c386 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.pos 247] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c387 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.pos 248] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c388 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 102, Sat.Literal.pos 249] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c389 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 103, Sat.Literal.pos 250] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 7) (5 : Fin 7)

theorem input_n7_c390 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 104, Sat.Literal.pos 251] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (0 : Fin 7) (6 : Fin 7)

theorem input_n7_c391 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.pos 255] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c392 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.pos 256] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c393 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 110, Sat.Literal.pos 257] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c394 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 111, Sat.Literal.pos 258] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (1 : Fin 7) (6 : Fin 7)

theorem input_n7_c395 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 113, Sat.Literal.pos 260] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 7) (1 : Fin 7)

theorem input_n7_c396 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.pos 263] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c397 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.pos 264] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c398 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 118, Sat.Literal.pos 265] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (2 : Fin 7) (6 : Fin 7)

theorem input_n7_c399 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 119, Sat.Literal.pos 266] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c400 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 121, Sat.Literal.pos 268] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 7) (2 : Fin 7)

theorem input_n7_c401 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.pos 270] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c402 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.pos 271] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c403 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 125, Sat.Literal.pos 272] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c404 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 126, Sat.Literal.pos 273] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c405 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 127, Sat.Literal.pos 274] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c406 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 128, Sat.Literal.pos 275] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c407 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 129, Sat.Literal.pos 276] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (3 : Fin 7)

theorem input_n7_c408 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 131, Sat.Literal.pos 278] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c409 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 132, Sat.Literal.pos 279] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c410 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 133, Sat.Literal.pos 280] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c411 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 134, Sat.Literal.pos 281] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c412 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 135, Sat.Literal.pos 282] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c413 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 136, Sat.Literal.pos 283] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c414 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 137, Sat.Literal.pos 284] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (4 : Fin 7)

theorem input_n7_c415 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 139, Sat.Literal.pos 286] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c416 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 140, Sat.Literal.pos 287] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c417 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 141, Sat.Literal.pos 288] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c418 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 142, Sat.Literal.pos 289] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c419 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 143, Sat.Literal.pos 290] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c420 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 144, Sat.Literal.pos 291] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c421 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 145, Sat.Literal.pos 292] :=
  h.toModel.arc_reach_clause (2 : Fin 3) (6 : Fin 7) (5 : Fin 7)

theorem input_n7_c422 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 247, Sat.Literal.neg 263, Sat.Literal.pos 249] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c423 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 247, Sat.Literal.neg 264, Sat.Literal.pos 250] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c424 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 248, Sat.Literal.neg 270, Sat.Literal.pos 249] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c425 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 248, Sat.Literal.neg 271, Sat.Literal.pos 250] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c426 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 248, Sat.Literal.neg 272, Sat.Literal.pos 251] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c427 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 249, Sat.Literal.neg 278, Sat.Literal.pos 250] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c428 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 249, Sat.Literal.neg 279, Sat.Literal.pos 251] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c429 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 250, Sat.Literal.neg 286, Sat.Literal.pos 251] :=
  h.toModel.trans_clause (2 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c430 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 255, Sat.Literal.neg 266, Sat.Literal.pos 252] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (0 : Fin 7)

theorem input_n7_c431 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 255, Sat.Literal.neg 270, Sat.Literal.pos 256] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c432 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 255, Sat.Literal.neg 271, Sat.Literal.pos 257] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c433 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 255, Sat.Literal.neg 272, Sat.Literal.pos 258] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7)

theorem input_n7_c434 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 256, Sat.Literal.neg 273, Sat.Literal.pos 252] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c435 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 256, Sat.Literal.neg 278, Sat.Literal.pos 257] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c436 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 256, Sat.Literal.neg 279, Sat.Literal.pos 258] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c437 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 257, Sat.Literal.neg 280, Sat.Literal.pos 252] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c438 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 257, Sat.Literal.neg 286, Sat.Literal.pos 258] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c439 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 258, Sat.Literal.neg 287, Sat.Literal.pos 252] :=
  h.toModel.trans_clause (2 : Fin 3) (1 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c440 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 263, Sat.Literal.neg 274, Sat.Literal.pos 260] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (1 : Fin 7)

theorem input_n7_c441 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 263, Sat.Literal.neg 278, Sat.Literal.pos 264] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c442 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 263, Sat.Literal.neg 279, Sat.Literal.pos 265] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c443 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 264, Sat.Literal.neg 281, Sat.Literal.pos 260] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c444 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 264, Sat.Literal.neg 286, Sat.Literal.pos 265] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c445 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 265, Sat.Literal.neg 288, Sat.Literal.pos 260] :=
  h.toModel.trans_clause (2 : Fin 3) (2 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c446 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 266, Sat.Literal.neg 247, Sat.Literal.pos 268] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c447 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 270, Sat.Literal.neg 273, Sat.Literal.pos 266] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (0 : Fin 7)

theorem input_n7_c448 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 270, Sat.Literal.neg 275, Sat.Literal.pos 268] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (2 : Fin 7)

theorem input_n7_c449 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 270, Sat.Literal.neg 279, Sat.Literal.pos 272] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7)

theorem input_n7_c450 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 271, Sat.Literal.neg 280, Sat.Literal.pos 266] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c451 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 271, Sat.Literal.neg 282, Sat.Literal.pos 268] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (2 : Fin 7)

theorem input_n7_c452 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 271, Sat.Literal.neg 286, Sat.Literal.pos 272] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c453 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 272, Sat.Literal.neg 287, Sat.Literal.pos 266] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c454 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 272, Sat.Literal.neg 289, Sat.Literal.pos 268] :=
  h.toModel.trans_clause (2 : Fin 3) (3 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c455 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 273, Sat.Literal.neg 247, Sat.Literal.pos 275] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c456 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 273, Sat.Literal.neg 248, Sat.Literal.pos 276] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c457 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 274, Sat.Literal.neg 255, Sat.Literal.pos 276] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c458 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 278, Sat.Literal.neg 280, Sat.Literal.pos 273] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (0 : Fin 7)

theorem input_n7_c459 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 278, Sat.Literal.neg 281, Sat.Literal.pos 274] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (1 : Fin 7)

theorem input_n7_c460 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 278, Sat.Literal.neg 283, Sat.Literal.pos 276] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (3 : Fin 7)

theorem input_n7_c461 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 278, Sat.Literal.neg 286, Sat.Literal.pos 279] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7)

theorem input_n7_c462 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 279, Sat.Literal.neg 287, Sat.Literal.pos 273] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c463 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 279, Sat.Literal.neg 288, Sat.Literal.pos 274] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c464 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 279, Sat.Literal.neg 289, Sat.Literal.pos 275] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c465 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 279, Sat.Literal.neg 290, Sat.Literal.pos 276] :=
  h.toModel.trans_clause (2 : Fin 3) (4 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c466 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 280, Sat.Literal.neg 248, Sat.Literal.pos 283] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c467 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 280, Sat.Literal.neg 249, Sat.Literal.pos 284] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c468 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 281, Sat.Literal.neg 255, Sat.Literal.pos 283] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c469 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 281, Sat.Literal.neg 256, Sat.Literal.pos 284] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c470 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 282, Sat.Literal.neg 263, Sat.Literal.pos 284] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c471 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 283, Sat.Literal.neg 270, Sat.Literal.pos 284] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c472 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 287, Sat.Literal.pos 280] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (0 : Fin 7)

theorem input_n7_c473 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 288, Sat.Literal.pos 281] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (1 : Fin 7)

theorem input_n7_c474 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 289, Sat.Literal.pos 282] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (2 : Fin 7)

theorem input_n7_c475 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 290, Sat.Literal.pos 283] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (3 : Fin 7)

theorem input_n7_c476 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 286, Sat.Literal.neg 291, Sat.Literal.pos 284] :=
  h.toModel.trans_clause (2 : Fin 3) (5 : Fin 7) (6 : Fin 7) (4 : Fin 7)

theorem input_n7_c477 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 287, Sat.Literal.neg 247, Sat.Literal.pos 289] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (2 : Fin 7)

theorem input_n7_c478 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 287, Sat.Literal.neg 248, Sat.Literal.pos 290] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (3 : Fin 7)

theorem input_n7_c479 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 287, Sat.Literal.neg 249, Sat.Literal.pos 291] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (4 : Fin 7)

theorem input_n7_c480 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 287, Sat.Literal.neg 250, Sat.Literal.pos 292] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (0 : Fin 7) (5 : Fin 7)

theorem input_n7_c481 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 288, Sat.Literal.neg 255, Sat.Literal.pos 290] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (1 : Fin 7) (3 : Fin 7)

theorem input_n7_c482 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 288, Sat.Literal.neg 256, Sat.Literal.pos 291] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (1 : Fin 7) (4 : Fin 7)

theorem input_n7_c483 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 288, Sat.Literal.neg 257, Sat.Literal.pos 292] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (1 : Fin 7) (5 : Fin 7)

theorem input_n7_c484 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 289, Sat.Literal.neg 263, Sat.Literal.pos 291] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (2 : Fin 7) (4 : Fin 7)

theorem input_n7_c485 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 289, Sat.Literal.neg 264, Sat.Literal.pos 292] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (2 : Fin 7) (5 : Fin 7)

theorem input_n7_c486 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 290, Sat.Literal.neg 270, Sat.Literal.pos 291] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (4 : Fin 7)

theorem input_n7_c487 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 290, Sat.Literal.neg 271, Sat.Literal.pos 292] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (3 : Fin 7) (5 : Fin 7)

theorem input_n7_c488 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 291, Sat.Literal.neg 278, Sat.Literal.pos 292] :=
  h.toModel.trans_clause (2 : Fin 3) (6 : Fin 7) (4 : Fin 7) (5 : Fin 7)

theorem input_n7_c489 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 153] :=
  h.toModel.predecessor_clause (0 : Fin 3) (6 : Fin 7)

theorem input_n7_c490 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 202] :=
  h.toModel.predecessor_clause (1 : Fin 3) (6 : Fin 7)

theorem input_n7_c491 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 251] :=
  h.toModel.predecessor_clause (2 : Fin 3) (6 : Fin 7)

theorem input_n7_c492 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 1, Sat.Literal.pos 50, Sat.Literal.pos 99] :=
  h.toModel.cycle_options_clause (0 : Fin 7)

theorem input_n7_c493 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 154] :=
  h.toModel.predecessor_clause (0 : Fin 3) (0 : Fin 7)

theorem input_n7_c494 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 203] :=
  h.toModel.predecessor_clause (1 : Fin 3) (0 : Fin 7)

theorem input_n7_c495 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 252] :=
  h.toModel.predecessor_clause (2 : Fin 3) (0 : Fin 7)

theorem input_n7_c496 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 9, Sat.Literal.pos 58, Sat.Literal.pos 107] :=
  h.toModel.cycle_options_clause (1 : Fin 7)

theorem input_n7_c497 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 162] :=
  h.toModel.predecessor_clause (0 : Fin 3) (1 : Fin 7)

theorem input_n7_c498 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 211] :=
  h.toModel.predecessor_clause (1 : Fin 3) (1 : Fin 7)

theorem input_n7_c499 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 260] :=
  h.toModel.predecessor_clause (2 : Fin 3) (1 : Fin 7)

theorem input_n7_c500 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 17, Sat.Literal.pos 66, Sat.Literal.pos 115] :=
  h.toModel.cycle_options_clause (2 : Fin 7)

theorem input_n7_c501 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 170] :=
  h.toModel.predecessor_clause (0 : Fin 3) (2 : Fin 7)

theorem input_n7_c502 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 219] :=
  h.toModel.predecessor_clause (1 : Fin 3) (2 : Fin 7)

theorem input_n7_c503 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 268] :=
  h.toModel.predecessor_clause (2 : Fin 3) (2 : Fin 7)

theorem input_n7_c504 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 25, Sat.Literal.pos 74, Sat.Literal.pos 123] :=
  h.toModel.cycle_options_clause (3 : Fin 7)

theorem input_n7_c505 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 178] :=
  h.toModel.predecessor_clause (0 : Fin 3) (3 : Fin 7)

theorem input_n7_c506 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 227] :=
  h.toModel.predecessor_clause (1 : Fin 3) (3 : Fin 7)

theorem input_n7_c507 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 276] :=
  h.toModel.predecessor_clause (2 : Fin 3) (3 : Fin 7)

theorem input_n7_c508 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 33, Sat.Literal.pos 82, Sat.Literal.pos 131] :=
  h.toModel.cycle_options_clause (4 : Fin 7)

theorem input_n7_c509 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 186] :=
  h.toModel.predecessor_clause (0 : Fin 3) (4 : Fin 7)

theorem input_n7_c510 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 235] :=
  h.toModel.predecessor_clause (1 : Fin 3) (4 : Fin 7)

theorem input_n7_c511 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 284] :=
  h.toModel.predecessor_clause (2 : Fin 3) (4 : Fin 7)

theorem input_n7_c512 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.pos 41, Sat.Literal.pos 90, Sat.Literal.pos 139] :=
  h.toModel.cycle_options_clause (5 : Fin 7)

theorem input_n7_c513 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 194] :=
  h.toModel.predecessor_clause (0 : Fin 3) (5 : Fin 7)

theorem input_n7_c514 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 243] :=
  h.toModel.predecessor_clause (1 : Fin 3) (5 : Fin 7)

theorem input_n7_c515 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 292] :=
  h.toModel.predecessor_clause (2 : Fin 3) (5 : Fin 7)

theorem input_n7_c516 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 58, Sat.Literal.neg 112] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (1 : Fin 7) (2 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c517 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 59, Sat.Literal.neg 119] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (1 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c518 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 108, Sat.Literal.neg 70] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (1 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c519 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 60, Sat.Literal.neg 126] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (1 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c520 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 109, Sat.Literal.neg 77] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (1 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c521 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 61, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (1 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c522 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 110, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (1 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c523 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 62, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (1 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c524 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 111, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (1 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c525 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 17, Sat.Literal.neg 119] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c526 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.neg 17, Sat.Literal.neg 70] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c527 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 116, Sat.Literal.neg 77] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c528 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 18, Sat.Literal.neg 126] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c529 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 116, Sat.Literal.neg 28] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c530 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.neg 18, Sat.Literal.neg 77] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c531 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.neg 67, Sat.Literal.neg 28] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c532 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 68, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c533 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 19, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c534 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.neg 19, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c535 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 100, Sat.Literal.neg 68, Sat.Literal.neg 35] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c536 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 69, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c537 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 2, Sat.Literal.neg 118, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c538 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 51, Sat.Literal.neg 20, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c539 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 74, Sat.Literal.neg 126] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c540 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 123, Sat.Literal.neg 77] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c541 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 25, Sat.Literal.neg 126] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c542 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 123, Sat.Literal.neg 28] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c543 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.neg 25, Sat.Literal.neg 77] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c544 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.neg 74, Sat.Literal.neg 28] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c545 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 75, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c546 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 124, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c547 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 26, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c548 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 124, Sat.Literal.neg 35] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c549 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.neg 26, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c550 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.neg 75, Sat.Literal.neg 35] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c551 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 76, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c552 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 3, Sat.Literal.neg 125, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c553 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 52, Sat.Literal.neg 27, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c554 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 101, Sat.Literal.neg 27, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c555 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 82, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c556 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 131, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c557 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 33, Sat.Literal.neg 133] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c558 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 131, Sat.Literal.neg 35] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c559 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 102, Sat.Literal.neg 33, Sat.Literal.neg 84] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c560 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 102, Sat.Literal.neg 82, Sat.Literal.neg 35] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (0 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c561 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 83, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c562 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 4, Sat.Literal.neg 132, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c563 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 53, Sat.Literal.neg 34, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c564 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 102, Sat.Literal.neg 34, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c565 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.neg 90, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c566 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 5, Sat.Literal.neg 139, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c567 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 54, Sat.Literal.neg 41, Sat.Literal.neg 140] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c568 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 103, Sat.Literal.neg 41, Sat.Literal.neg 91] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (0 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c569 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 66, Sat.Literal.neg 120] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c570 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 17, Sat.Literal.neg 120] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c571 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 115, Sat.Literal.neg 22] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c572 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 67, Sat.Literal.neg 127] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c573 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 116, Sat.Literal.neg 78] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c574 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 18, Sat.Literal.neg 127] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c575 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 116, Sat.Literal.neg 29] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c576 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 68, Sat.Literal.neg 134] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c577 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 117, Sat.Literal.neg 85] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c578 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 19, Sat.Literal.neg 134] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c579 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 117, Sat.Literal.neg 36] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c580 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 69, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c581 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 9, Sat.Literal.neg 118, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c582 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 20, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c583 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 58, Sat.Literal.neg 118, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (2 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c584 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 74, Sat.Literal.neg 127] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c585 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 123, Sat.Literal.neg 78] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c586 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 123, Sat.Literal.neg 29] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c587 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 25, Sat.Literal.neg 78] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c588 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 74, Sat.Literal.neg 29] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c589 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 75, Sat.Literal.neg 134] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c590 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 26, Sat.Literal.neg 134] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c591 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 124, Sat.Literal.neg 36] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c592 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 26, Sat.Literal.neg 85] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c593 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 75, Sat.Literal.neg 36] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c594 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 76, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c595 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 10, Sat.Literal.neg 125, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c596 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 27, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c597 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 59, Sat.Literal.neg 125, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c598 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 27, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c599 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 108, Sat.Literal.neg 76, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c600 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 82, Sat.Literal.neg 134] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c601 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 131, Sat.Literal.neg 85] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c602 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 131, Sat.Literal.neg 36] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c603 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 33, Sat.Literal.neg 85] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c604 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 82, Sat.Literal.neg 36] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c605 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 83, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c606 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 11, Sat.Literal.neg 132, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c607 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 34, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c608 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 60, Sat.Literal.neg 132, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c609 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 34, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c610 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 109, Sat.Literal.neg 83, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c611 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.neg 90, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c612 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 12, Sat.Literal.neg 139, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c613 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.neg 41, Sat.Literal.neg 141] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c614 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 61, Sat.Literal.neg 139, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c615 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 110, Sat.Literal.neg 41, Sat.Literal.neg 92] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c616 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 110, Sat.Literal.neg 90, Sat.Literal.neg 43] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c617 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 74, Sat.Literal.neg 128] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c618 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 123, Sat.Literal.neg 79] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c619 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 25, Sat.Literal.neg 128] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c620 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 123, Sat.Literal.neg 30] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c621 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 75, Sat.Literal.neg 135] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c622 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 124, Sat.Literal.neg 86] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c623 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 26, Sat.Literal.neg 135] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c624 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 124, Sat.Literal.neg 37] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c625 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 76, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c626 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 17, Sat.Literal.neg 125, Sat.Literal.neg 93] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c627 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 27, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c628 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 66, Sat.Literal.neg 125, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (3 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c629 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 82, Sat.Literal.neg 135] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c630 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 131, Sat.Literal.neg 86] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c631 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.neg 33, Sat.Literal.neg 135] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c632 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.neg 131, Sat.Literal.neg 37] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c633 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 33, Sat.Literal.neg 86] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c634 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 82, Sat.Literal.neg 37] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c635 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 83, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c636 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 18, Sat.Literal.neg 132, Sat.Literal.neg 93] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c637 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.neg 34, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c638 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 67, Sat.Literal.neg 132, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c639 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 34, Sat.Literal.neg 93] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c640 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 116, Sat.Literal.neg 83, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (2 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c641 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 90, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c642 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 19, Sat.Literal.neg 139, Sat.Literal.neg 93] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c643 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.neg 41, Sat.Literal.neg 142] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c644 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 68, Sat.Literal.neg 139, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c645 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 41, Sat.Literal.neg 93] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c646 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 117, Sat.Literal.neg 90, Sat.Literal.neg 44] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (2 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c647 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 82, Sat.Literal.neg 136] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c648 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 131, Sat.Literal.neg 87] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c649 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 33, Sat.Literal.neg 136] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c650 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 131, Sat.Literal.neg 38] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c651 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 33, Sat.Literal.neg 87] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c652 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 82, Sat.Literal.neg 38] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c653 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 83, Sat.Literal.neg 143] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c654 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 25, Sat.Literal.neg 132, Sat.Literal.neg 94] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c655 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 34, Sat.Literal.neg 143] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c656 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 74, Sat.Literal.neg 132, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c657 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 34, Sat.Literal.neg 94] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c658 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 123, Sat.Literal.neg 83, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (3 : Fin 7) (4 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c659 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 90, Sat.Literal.neg 143] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c660 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 26, Sat.Literal.neg 139, Sat.Literal.neg 94] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c661 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 41, Sat.Literal.neg 143] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c662 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 75, Sat.Literal.neg 139, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c663 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 41, Sat.Literal.neg 94] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c664 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 124, Sat.Literal.neg 90, Sat.Literal.neg 45] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (3 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c665 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 90, Sat.Literal.neg 144] :=
  h.toModel.rainbow_clause (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c666 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 33, Sat.Literal.neg 139, Sat.Literal.neg 95] :=
  h.toModel.rainbow_clause (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c667 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 41, Sat.Literal.neg 144] :=
  h.toModel.rainbow_clause (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c668 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 82, Sat.Literal.neg 139, Sat.Literal.neg 46] :=
  h.toModel.rainbow_clause (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c669 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 131, Sat.Literal.neg 41, Sat.Literal.neg 95] :=
  h.toModel.rainbow_clause (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c670 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 131, Sat.Literal.neg 90, Sat.Literal.neg 46] :=
  h.toModel.rainbow_clause (2 : Fin 3) (1 : Fin 3) (0 : Fin 3) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem input_n7_c671 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 1, Sat.Literal.pos 294] :=
  h.first_advance_clause 0 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c672 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 99, Sat.Literal.neg 99] :=
  h.first_conflict_clause 0 (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c673 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 294, Sat.Literal.neg 9, Sat.Literal.neg 9, Sat.Literal.pos 295] :=
  h.advance_clause 0 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c674 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 294, Sat.Literal.neg 107, Sat.Literal.neg 107] :=
  h.conflict_clause 0 (0 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c675 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 295, Sat.Literal.neg 17, Sat.Literal.neg 17, Sat.Literal.pos 296] :=
  h.advance_clause 0 (1 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c676 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 295, Sat.Literal.neg 115, Sat.Literal.neg 115] :=
  h.conflict_clause 0 (1 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c677 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 296, Sat.Literal.neg 25, Sat.Literal.neg 25, Sat.Literal.pos 297] :=
  h.advance_clause 0 (2 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c678 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 296, Sat.Literal.neg 123, Sat.Literal.neg 123] :=
  h.conflict_clause 0 (2 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c679 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 297, Sat.Literal.neg 33, Sat.Literal.neg 33, Sat.Literal.pos 298] :=
  h.advance_clause 0 (3 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c680 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 297, Sat.Literal.neg 131, Sat.Literal.neg 131] :=
  h.conflict_clause 0 (3 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c681 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 298, Sat.Literal.neg 139, Sat.Literal.neg 139] :=
  h.conflict_clause 0 (4 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c682 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 50, Sat.Literal.neg 50] :=
  h.first_conflict_clause 1 (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c683 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 58, Sat.Literal.pos 336] :=
  h.first_advance_clause 7 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c684 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 336, Sat.Literal.neg 58, Sat.Literal.neg 66] :=
  h.conflict_clause 7 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c685 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 58, Sat.Literal.pos 348] :=
  h.first_advance_clause 9 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c686 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 348, Sat.Literal.neg 58, Sat.Literal.neg 115, Sat.Literal.pos 349] :=
  h.advance_clause 9 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c687 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 349, Sat.Literal.neg 115, Sat.Literal.neg 74] :=
  h.conflict_clause 9 (1 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c688 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 17, Sat.Literal.pos 360] :=
  h.first_advance_clause 11 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c689 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 360, Sat.Literal.neg 58, Sat.Literal.neg 25] :=
  h.conflict_clause 11 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c690 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 66, Sat.Literal.pos 372] :=
  h.first_advance_clause 13 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c691 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 372, Sat.Literal.neg 9, Sat.Literal.neg 74, Sat.Literal.pos 373] :=
  h.advance_clause 13 (0 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c692 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 373, Sat.Literal.neg 66, Sat.Literal.neg 33, Sat.Literal.pos 374] :=
  h.advance_clause 13 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c693 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 373, Sat.Literal.neg 66, Sat.Literal.neg 82] :=
  h.conflict_clause 13 (1 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c694 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 374, Sat.Literal.neg 74, Sat.Literal.neg 90] :=
  h.conflict_clause 13 (2 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c695 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 115, Sat.Literal.pos 378] :=
  h.first_advance_clause 14 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c696 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 378, Sat.Literal.neg 58, Sat.Literal.neg 25, Sat.Literal.pos 379] :=
  h.advance_clause 14 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c697 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 378, Sat.Literal.neg 58, Sat.Literal.neg 123] :=
  h.conflict_clause 14 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c698 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 379, Sat.Literal.neg 115, Sat.Literal.neg 131] :=
  h.conflict_clause 14 (1 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c699 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 66, Sat.Literal.pos 384] :=
  h.first_advance_clause 15 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c700 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 384, Sat.Literal.neg 9, Sat.Literal.neg 74, Sat.Literal.pos 385] :=
  h.advance_clause 15 (0 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c701 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 385, Sat.Literal.neg 66, Sat.Literal.neg 131, Sat.Literal.pos 386] :=
  h.advance_clause 15 (1 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c702 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 386, Sat.Literal.neg 74, Sat.Literal.neg 90] :=
  h.conflict_clause 15 (2 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c703 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 386, Sat.Literal.neg 74, Sat.Literal.neg 139, Sat.Literal.pos 387] :=
  h.advance_clause 15 (2 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c704 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 387, Sat.Literal.neg 131, Sat.Literal.neg 91] :=
  h.conflict_clause 15 (3 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c705 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 387, Sat.Literal.neg 131, Sat.Literal.neg 140] :=
  h.conflict_clause 15 (3 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c706 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 25, Sat.Literal.pos 396] :=
  h.first_advance_clause 17 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c707 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 396, Sat.Literal.neg 9, Sat.Literal.neg 33, Sat.Literal.pos 397] :=
  h.advance_clause 17 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c708 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 396, Sat.Literal.neg 58, Sat.Literal.neg 33] :=
  h.conflict_clause 17 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c709 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 396, Sat.Literal.neg 58, Sat.Literal.neg 82, Sat.Literal.pos 397] :=
  h.advance_clause 17 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c710 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 397, Sat.Literal.neg 66, Sat.Literal.neg 41] :=
  h.conflict_clause 17 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c711 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 397, Sat.Literal.neg 115, Sat.Literal.neg 41] :=
  h.conflict_clause 17 (1 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c712 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 25, Sat.Literal.pos 402] :=
  h.first_advance_clause 18 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c713 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 402, Sat.Literal.neg 58, Sat.Literal.neg 131, Sat.Literal.pos 403] :=
  h.advance_clause 18 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c714 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 403, Sat.Literal.neg 115, Sat.Literal.neg 41] :=
  h.conflict_clause 18 (1 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c715 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 74, Sat.Literal.pos 408] :=
  h.first_advance_clause 19 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c716 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 408, Sat.Literal.neg 9, Sat.Literal.neg 82, Sat.Literal.pos 409] :=
  h.advance_clause 19 (0 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c717 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 408, Sat.Literal.neg 58, Sat.Literal.neg 82] :=
  h.conflict_clause 19 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c718 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 409, Sat.Literal.neg 17, Sat.Literal.neg 90, Sat.Literal.pos 410] :=
  h.advance_clause 19 (1 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c719 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 410, Sat.Literal.neg 74, Sat.Literal.neg 91] :=
  h.conflict_clause 19 (2 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c720 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 123, Sat.Literal.pos 414] :=
  h.first_advance_clause 20 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c721 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 414, Sat.Literal.neg 9, Sat.Literal.neg 131, Sat.Literal.pos 415] :=
  h.advance_clause 20 (0 : Fin 6) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c722 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 414, Sat.Literal.neg 58, Sat.Literal.neg 131] :=
  h.conflict_clause 20 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c723 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 415, Sat.Literal.neg 66, Sat.Literal.neg 41, Sat.Literal.pos 416] :=
  h.advance_clause 20 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c724 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 415, Sat.Literal.neg 66, Sat.Literal.neg 139] :=
  h.conflict_clause 20 (1 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c725 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 416, Sat.Literal.neg 123, Sat.Literal.neg 91, Sat.Literal.pos 417] :=
  h.advance_clause 20 (2 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c726 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 416, Sat.Literal.neg 123, Sat.Literal.neg 140] :=
  h.conflict_clause 20 (2 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c727 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 417, Sat.Literal.neg 131, Sat.Literal.neg 1] :=
  h.conflict_clause 20 (3 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c728 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 74, Sat.Literal.pos 420] :=
  h.first_advance_clause 21 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c729 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 420, Sat.Literal.neg 58, Sat.Literal.neg 131, Sat.Literal.pos 421] :=
  h.advance_clause 21 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c730 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 421, Sat.Literal.neg 17, Sat.Literal.neg 90, Sat.Literal.pos 422] :=
  h.advance_clause 21 (1 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c731 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 422, Sat.Literal.neg 74, Sat.Literal.neg 140, Sat.Literal.pos 423] :=
  h.advance_clause 21 (2 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c732 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 423, Sat.Literal.neg 131, Sat.Literal.neg 1, Sat.Literal.pos 424] :=
  h.advance_clause 21 (3 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c733 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 424, Sat.Literal.neg 90, Sat.Literal.neg 58] :=
  h.conflict_clause 21 (4 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c734 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 123, Sat.Literal.pos 426] :=
  h.first_advance_clause 22 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c735 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 426, Sat.Literal.neg 9, Sat.Literal.neg 131, Sat.Literal.pos 427] :=
  h.advance_clause 22 (0 : Fin 6) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c736 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 427, Sat.Literal.neg 66, Sat.Literal.neg 90, Sat.Literal.pos 428] :=
  h.advance_clause 22 (1 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c737 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 428, Sat.Literal.neg 123, Sat.Literal.neg 91] :=
  h.conflict_clause 22 (2 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c738 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 428, Sat.Literal.neg 123, Sat.Literal.neg 140] :=
  h.conflict_clause 22 (2 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c739 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 33, Sat.Literal.pos 432] :=
  h.first_advance_clause 23 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c740 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 432, Sat.Literal.neg 9, Sat.Literal.neg 41, Sat.Literal.pos 433] :=
  h.advance_clause 23 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c741 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 432, Sat.Literal.neg 58, Sat.Literal.neg 41] :=
  h.conflict_clause 23 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c742 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 432, Sat.Literal.neg 58, Sat.Literal.neg 90, Sat.Literal.pos 433] :=
  h.advance_clause 23 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c743 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 433, Sat.Literal.neg 66, Sat.Literal.neg 91, Sat.Literal.pos 434] :=
  h.advance_clause 23 (1 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c744 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 433, Sat.Literal.neg 115, Sat.Literal.neg 140, Sat.Literal.pos 434] :=
  h.advance_clause 23 (1 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c745 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 434, Sat.Literal.neg 74, Sat.Literal.neg 1] :=
  h.conflict_clause 23 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c746 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 434, Sat.Literal.neg 123, Sat.Literal.neg 1] :=
  h.conflict_clause 23 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c747 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 33, Sat.Literal.pos 438] :=
  h.first_advance_clause 24 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c748 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 438, Sat.Literal.neg 9, Sat.Literal.neg 41, Sat.Literal.pos 439] :=
  h.advance_clause 24 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c749 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 439, Sat.Literal.neg 66, Sat.Literal.neg 140, Sat.Literal.pos 440] :=
  h.advance_clause 24 (1 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c750 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 440, Sat.Literal.neg 74, Sat.Literal.neg 1] :=
  h.conflict_clause 24 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c751 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 440, Sat.Literal.neg 123, Sat.Literal.neg 1] :=
  h.conflict_clause 24 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c752 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 82, Sat.Literal.pos 444] :=
  h.first_advance_clause 25 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c753 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 444, Sat.Literal.neg 9, Sat.Literal.neg 90, Sat.Literal.pos 445] :=
  h.advance_clause 25 (0 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c754 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 444, Sat.Literal.neg 58, Sat.Literal.neg 90] :=
  h.conflict_clause 25 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c755 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 445, Sat.Literal.neg 66, Sat.Literal.neg 91] :=
  h.conflict_clause 25 (1 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c756 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 131, Sat.Literal.pos 450] :=
  h.first_advance_clause 26 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c757 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 450, Sat.Literal.neg 9, Sat.Literal.neg 139, Sat.Literal.pos 451] :=
  h.advance_clause 26 (0 : Fin 6) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c758 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 450, Sat.Literal.neg 58, Sat.Literal.neg 41, Sat.Literal.pos 451] :=
  h.advance_clause 26 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c759 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 450, Sat.Literal.neg 58, Sat.Literal.neg 139] :=
  h.conflict_clause 26 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c760 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 451, Sat.Literal.neg 17, Sat.Literal.neg 140, Sat.Literal.pos 452] :=
  h.advance_clause 26 (1 : Fin 6) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c761 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 451, Sat.Literal.neg 66, Sat.Literal.neg 140] :=
  h.conflict_clause 26 (1 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c762 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 451, Sat.Literal.neg 115, Sat.Literal.neg 140] :=
  h.conflict_clause 26 (1 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c763 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 452, Sat.Literal.neg 74, Sat.Literal.neg 1, Sat.Literal.pos 453] :=
  h.advance_clause 26 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c764 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 453, Sat.Literal.neg 131, Sat.Literal.neg 9] :=
  h.conflict_clause 26 (3 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c765 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 82, Sat.Literal.pos 456] :=
  h.first_advance_clause 27 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c766 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 456, Sat.Literal.neg 58, Sat.Literal.neg 139, Sat.Literal.pos 457] :=
  h.advance_clause 27 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c767 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 457, Sat.Literal.neg 115, Sat.Literal.neg 91] :=
  h.conflict_clause 27 (1 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c768 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 131, Sat.Literal.pos 462] :=
  h.first_advance_clause 28 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c769 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 462, Sat.Literal.neg 58, Sat.Literal.neg 90, Sat.Literal.pos 463] :=
  h.advance_clause 28 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c770 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 463, Sat.Literal.neg 115, Sat.Literal.neg 140] :=
  h.conflict_clause 28 (1 : Fin 6) (2 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c771 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 41, Sat.Literal.pos 468] :=
  h.first_advance_clause 29 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c772 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 468, Sat.Literal.neg 9, Sat.Literal.neg 42, Sat.Literal.pos 469] :=
  h.advance_clause 29 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c773 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 468, Sat.Literal.neg 58, Sat.Literal.neg 91, Sat.Literal.pos 469] :=
  h.advance_clause 29 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c774 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 469, Sat.Literal.neg 17, Sat.Literal.neg 1, Sat.Literal.pos 470] :=
  h.advance_clause 29 (1 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c775 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 469, Sat.Literal.neg 115, Sat.Literal.neg 1] :=
  h.conflict_clause 29 (1 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c776 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 470, Sat.Literal.neg 25, Sat.Literal.neg 9, Sat.Literal.pos 471] :=
  h.advance_clause 29 (2 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c777 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 470, Sat.Literal.neg 74, Sat.Literal.neg 58, Sat.Literal.pos 471] :=
  h.advance_clause 29 (2 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c778 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 471, Sat.Literal.neg 82, Sat.Literal.neg 17] :=
  h.conflict_clause 29 (3 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c779 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 471, Sat.Literal.neg 131, Sat.Literal.neg 17] :=
  h.conflict_clause 29 (3 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c780 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 41, Sat.Literal.pos 474] :=
  h.first_advance_clause 30 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c781 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 474, Sat.Literal.neg 58, Sat.Literal.neg 140, Sat.Literal.pos 475] :=
  h.advance_clause 30 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c782 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 475, Sat.Literal.neg 17, Sat.Literal.neg 1, Sat.Literal.pos 476] :=
  h.advance_clause 30 (1 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c783 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 476, Sat.Literal.neg 123, Sat.Literal.neg 58, Sat.Literal.pos 477] :=
  h.advance_clause 30 (2 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c784 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 477, Sat.Literal.neg 82, Sat.Literal.neg 17] :=
  h.conflict_clause 30 (3 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c785 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 90, Sat.Literal.pos 480] :=
  h.first_advance_clause 31 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c786 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 480, Sat.Literal.neg 9, Sat.Literal.neg 91, Sat.Literal.pos 481] :=
  h.advance_clause 31 (0 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c787 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 480, Sat.Literal.neg 58, Sat.Literal.neg 91] :=
  h.conflict_clause 31 (0 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c788 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 481, Sat.Literal.neg 66, Sat.Literal.neg 1, Sat.Literal.pos 482] :=
  h.advance_clause 31 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c789 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 482, Sat.Literal.neg 74, Sat.Literal.neg 9, Sat.Literal.pos 483] :=
  h.advance_clause 31 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c790 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 482, Sat.Literal.neg 123, Sat.Literal.neg 9] :=
  h.conflict_clause 31 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c791 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 483, Sat.Literal.neg 82, Sat.Literal.neg 66] :=
  h.conflict_clause 31 (3 : Fin 6) (1 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c792 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 483, Sat.Literal.neg 131, Sat.Literal.neg 66] :=
  h.conflict_clause 31 (3 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c793 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 139, Sat.Literal.pos 486] :=
  h.first_advance_clause 32 (0 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c794 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 486, Sat.Literal.neg 9, Sat.Literal.neg 140, Sat.Literal.pos 487] :=
  h.advance_clause 32 (0 : Fin 6) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide)

theorem input_n7_c795 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 486, Sat.Literal.neg 58, Sat.Literal.neg 42, Sat.Literal.pos 487] :=
  h.advance_clause 32 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c796 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 486, Sat.Literal.neg 58, Sat.Literal.neg 140] :=
  h.conflict_clause 32 (0 : Fin 6) (1 : Fin 3) (2 : Fin 3) (by decide)

theorem input_n7_c797 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 487, Sat.Literal.neg 66, Sat.Literal.neg 1, Sat.Literal.pos 488] :=
  h.advance_clause 32 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c798 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 487, Sat.Literal.neg 115, Sat.Literal.neg 1] :=
  h.conflict_clause 32 (1 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c799 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 488, Sat.Literal.neg 123, Sat.Literal.neg 9] :=
  h.conflict_clause 32 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c800 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 42, Sat.Literal.pos 504] :=
  h.first_advance_clause 35 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c801 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 504, Sat.Literal.neg 9, Sat.Literal.neg 1, Sat.Literal.pos 505] :=
  h.advance_clause 35 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c802 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 504, Sat.Literal.neg 58, Sat.Literal.neg 1] :=
  h.conflict_clause 35 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c803 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 505, Sat.Literal.neg 17, Sat.Literal.neg 9, Sat.Literal.pos 506] :=
  h.advance_clause 35 (1 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c804 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 505, Sat.Literal.neg 66, Sat.Literal.neg 9] :=
  h.conflict_clause 35 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c805 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 506, Sat.Literal.neg 25, Sat.Literal.neg 17, Sat.Literal.pos 507] :=
  h.advance_clause 35 (2 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c806 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 506, Sat.Literal.neg 74, Sat.Literal.neg 17] :=
  h.conflict_clause 35 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c807 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 507, Sat.Literal.neg 82, Sat.Literal.neg 25] :=
  h.conflict_clause 35 (3 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c808 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 42, Sat.Literal.pos 510] :=
  h.first_advance_clause 36 (0 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c809 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 510, Sat.Literal.neg 9, Sat.Literal.neg 1, Sat.Literal.pos 511] :=
  h.advance_clause 36 (0 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c810 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 511, Sat.Literal.neg 17, Sat.Literal.neg 9, Sat.Literal.pos 512] :=
  h.advance_clause 36 (1 : Fin 6) (0 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c811 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 511, Sat.Literal.neg 66, Sat.Literal.neg 9] :=
  h.conflict_clause 36 (1 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c812 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 512, Sat.Literal.neg 74, Sat.Literal.neg 17] :=
  h.conflict_clause 36 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c813 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 512, Sat.Literal.neg 123, Sat.Literal.neg 17] :=
  h.conflict_clause 36 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c814 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 1, Sat.Literal.neg 91, Sat.Literal.pos 516] :=
  h.first_advance_clause 37 (0 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c815 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 516, Sat.Literal.neg 58, Sat.Literal.neg 1, Sat.Literal.pos 517] :=
  h.advance_clause 37 (0 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c816 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 517, Sat.Literal.neg 17, Sat.Literal.neg 58, Sat.Literal.pos 518] :=
  h.advance_clause 37 (1 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c817 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 517, Sat.Literal.neg 115, Sat.Literal.neg 9] :=
  h.conflict_clause 37 (1 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c818 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 517, Sat.Literal.neg 115, Sat.Literal.neg 58] :=
  h.conflict_clause 37 (1 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c819 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 518, Sat.Literal.neg 74, Sat.Literal.neg 17, Sat.Literal.pos 519] :=
  h.advance_clause 37 (2 : Fin 6) (1 : Fin 3) (0 : Fin 3) (by decide) (by decide)

theorem input_n7_c820 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 518, Sat.Literal.neg 123, Sat.Literal.neg 17] :=
  h.conflict_clause 37 (2 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

theorem input_n7_c821 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 518, Sat.Literal.neg 123, Sat.Literal.neg 66] :=
  h.conflict_clause 37 (2 : Fin 6) (2 : Fin 3) (1 : Fin 3) (by decide)

theorem input_n7_c822 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 519, Sat.Literal.neg 33, Sat.Literal.neg 74, Sat.Literal.pos 520] :=
  h.advance_clause 37 (3 : Fin 6) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)

theorem input_n7_c823 (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) :
    val.satisfies [Sat.Literal.neg 520, Sat.Literal.neg 139, Sat.Literal.neg 33] :=
  h.conflict_clause 37 (4 : Fin 6) (2 : Fin 3) (0 : Fin 3) (by decide)

lrat_proof cert_n7_root
  "p cnf 540 824\n3 15 52 64 101 113 0\n-3 -52 0\n-3 -64 0\n-3 -101 0\n-3 -113 0\n4 22 53 71 102 120 0\n-4 -102 0\n-53 -71 0\n-53 -102 0\n-53 -120 0\n5 29 54 78 103 127 0\n-5 -54 0\n-5 -78 0\n-5 -103 0\n-5 -127 0\n-29 -54 0\n-29 -103 0\n-54 -78 0\n-54 -103 0\n-54 -127 0\n-78 -127 0\n6 36 55 85 104 134 0\n-6 -36 0\n-6 -85 0\n-6 -134 0\n-36 -55 0\n-36 -85 0\n-36 -134 0\n-85 -104 0\n-104 -134 0\n7 43 56 92 105 141 0\n-43 -141 0\n-92 -141 0\n10 16 59 65 108 114 0\n11 23 60 72 109 121 0\n-11 -60 0\n-11 -109 0\n-60 -72 0\n-60 -109 0\n-60 -121 0\n12 30 61 79 110 128 0\n-12 -30 0\n-12 -61 0\n-12 -79 0\n-12 -110 0\n-12 -128 0\n-30 -61 0\n-30 -110 0\n-61 -79 0\n-61 -110 0\n-61 -128 0\n-79 -110 0\n-110 -128 0\n13 37 62 86 111 135 0\n-13 -37 0\n-13 -111 0\n-13 -135 0\n-37 -62 0\n-37 -86 0\n-37 -111 0\n-37 -135 0\n-62 -111 0\n14 44 63 93 112 142 0\n-44 -93 0\n-44 -142 0\n18 24 67 73 116 122 0\n-18 -67 0\n-18 -116 0\n19 31 68 80 117 129 0\n-19 -68 0\n-19 -117 0\n-19 -129 0\n-31 -68 0\n-31 -117 0\n-117 -129 0\n20 38 69 87 118 136 0\n-20 -38 0\n-20 -69 0\n-20 -136 0\n-38 -69 0\n-38 -118 0\n-69 -87 0\n-69 -118 0\n-69 -136 0\n-118 -136 0\n21 45 70 94 119 143 0\n-21 -70 0\n-45 -70 0\n-45 -143 0\n-70 -94 0\n-70 -119 0\n-94 -119 0\n-94 -143 0\n-119 -143 0\n26 32 75 81 124 130 0\n-26 -75 0\n-26 -124 0\n-75 -124 0\n27 39 76 88 125 137 0\n-27 -39 0\n-27 -76 0\n-27 -125 0\n-39 -76 0\n-76 -88 0\n-76 -125 0\n-76 -137 0\n28 46 77 95 126 144 0\n-28 -95 0\n-28 -144 0\n-46 -77 0\n-46 -126 0\n-46 -144 0\n-77 -95 0\n-77 -144 0\n-95 -126 0\n-95 -144 0\n-126 -144 0\n34 40 83 89 132 138 0\n-34 -83 0\n-34 -132 0\n-83 -132 0\n35 47 84 96 133 145 0\n-35 -84 0\n-35 -133 0\n-47 -84 0\n-47 -133 0\n-84 -96 0\n-84 -133 0\n-84 -145 0\n-96 -133 0\n-133 -145 0\n42 48 91 97 140 146 0\n-91 -140 0\n-2 149 0\n-3 150 0\n-4 151 0\n-5 152 0\n-6 153 0\n-7 154 0\n-10 157 0\n-11 158 0\n-12 159 0\n-13 160 0\n-14 161 0\n-15 162 0\n-16 163 0\n-18 165 0\n-19 166 0\n-20 167 0\n-21 168 0\n-22 169 0\n-23 170 0\n-24 171 0\n-26 173 0\n-27 174 0\n-28 175 0\n-29 176 0\n-30 177 0\n-31 178 0\n-32 179 0\n-34 181 0\n-35 182 0\n-36 183 0\n-37 184 0\n-38 185 0\n-39 186 0\n-40 187 0\n-42 189 0\n-43 190 0\n-44 191 0\n-45 192 0\n-46 193 0\n-47 194 0\n-48 195 0\n-149 -157 150 0\n-149 -158 151 0\n-149 -159 152 0\n-149 -161 154 0\n-150 -165 151 0\n-150 -166 152 0\n-150 -168 154 0\n-151 -173 152 0\n-151 -174 153 0\n-151 -175 154 0\n-152 -182 154 0\n-153 -189 154 0\n-157 -165 158 0\n-157 -166 159 0\n-157 -167 160 0\n-157 -168 161 0\n-158 -173 159 0\n-158 -174 160 0\n-158 -175 161 0\n-159 -176 155 0\n-159 -181 160 0\n-159 -182 161 0\n-160 -183 155 0\n-160 -189 161 0\n-162 -149 163 0\n-165 -169 162 0\n-165 -170 163 0\n-165 -173 166 0\n-165 -174 167 0\n-165 -175 168 0\n-166 -176 162 0\n-166 -177 163 0\n-166 -181 167 0\n-166 -182 168 0\n-167 -183 162 0\n-167 -184 163 0\n-167 -189 168 0\n-168 -191 163 0\n-169 -150 171 0\n-170 -157 171 0\n-173 -176 169 0\n-173 -177 170 0\n-173 -178 171 0\n-173 -181 174 0\n-173 -182 175 0\n-174 -183 169 0\n-174 -184 170 0\n-174 -185 171 0\n-174 -189 175 0\n-175 -191 170 0\n-175 -192 171 0\n-176 -149 177 0\n-176 -150 178 0\n-176 -151 179 0\n-177 -157 178 0\n-177 -158 179 0\n-178 -165 179 0\n-181 -183 176 0\n-181 -184 177 0\n-181 -185 178 0\n-181 -186 179 0\n-181 -189 182 0\n-182 -191 177 0\n-182 -192 178 0\n-182 -193 179 0\n-183 -149 184 0\n-183 -150 185 0\n-183 -151 186 0\n-183 -152 187 0\n-184 -157 185 0\n-184 -158 186 0\n-184 -159 187 0\n-185 -165 186 0\n-185 -166 187 0\n-186 -173 187 0\n-189 -191 184 0\n-189 -192 185 0\n-189 -193 186 0\n-189 -194 187 0\n-190 -149 191 0\n-191 -157 192 0\n-191 -158 193 0\n-191 -159 194 0\n-191 -160 195 0\n-192 -165 193 0\n-192 -166 194 0\n-192 -167 195 0\n-193 -173 194 0\n-193 -174 195 0\n-194 -181 195 0\n-52 199 0\n-53 200 0\n-54 201 0\n-55 202 0\n-56 203 0\n-59 206 0\n-60 207 0\n-61 208 0\n-62 209 0\n-63 210 0\n-64 211 0\n-65 212 0\n-67 214 0\n-68 215 0\n-69 216 0\n-70 217 0\n-71 218 0\n-72 219 0\n-73 220 0\n-75 222 0\n-76 223 0\n-77 224 0\n-78 225 0\n-79 226 0\n-80 227 0\n-81 228 0\n-83 230 0\n-84 231 0\n-85 232 0\n-86 233 0\n-87 234 0\n-88 235 0\n-89 236 0\n-91 238 0\n-92 239 0\n-93 240 0\n-94 241 0\n-95 242 0\n-96 243 0\n-97 244 0\n-199 -216 202 0\n-199 -217 203 0\n-200 -222 201 0\n-200 -223 202 0\n-200 -224 203 0\n-201 -230 202 0\n-201 -231 203 0\n-202 -238 203 0\n-206 -211 204 0\n-206 -215 208 0\n-206 -216 209 0\n-207 -218 204 0\n-207 -222 208 0\n-207 -223 209 0\n-207 -224 210 0\n-208 -225 204 0\n-208 -230 209 0\n-208 -231 210 0\n-209 -232 204 0\n-209 -238 210 0\n-210 -239 204 0\n-214 -219 212 0\n-214 -222 215 0\n-214 -223 216 0\n-214 -224 217 0\n-215 -225 211 0\n-215 -226 212 0\n-215 -230 216 0\n-215 -231 217 0\n-216 -232 211 0\n-216 -233 212 0\n-216 -238 217 0\n-217 -240 212 0\n-218 -199 220 0\n-219 -206 220 0\n-222 -226 219 0\n-222 -227 220 0\n-222 -230 223 0\n-222 -231 224 0\n-223 -232 218 0\n-223 -233 219 0\n-223 -234 220 0\n-223 -238 224 0\n-224 -240 219 0\n-224 -241 220 0\n-225 -200 228 0\n-226 -206 227 0\n-226 -207 228 0\n-227 -214 228 0\n-230 -232 225 0\n-230 -233 226 0\n-230 -234 227 0\n-230 -235 228 0\n-230 -238 231 0\n-231 -239 225 0\n-231 -240 226 0\n-231 -241 227 0\n-231 -242 228 0\n-232 -200 235 0\n-232 -201 236 0\n-233 -207 235 0\n-233 -208 236 0\n-234 -214 235 0\n-234 -215 236 0\n-235 -222 236 0\n-238 -239 232 0\n-238 -240 233 0\n-238 -241 234 0\n-238 -242 235 0\n-238 -243 236 0\n-239 -200 242 0\n-239 -201 243 0\n-239 -202 244 0\n-240 -207 242 0\n-240 -208 243 0\n-240 -209 244 0\n-241 -214 242 0\n-241 -215 243 0\n-241 -216 244 0\n-242 -222 243 0\n-242 -223 244 0\n-243 -230 244 0\n-101 248 0\n-102 249 0\n-103 250 0\n-104 251 0\n-105 252 0\n-109 256 0\n-110 257 0\n-111 258 0\n-112 259 0\n-114 261 0\n-117 264 0\n-118 265 0\n-119 266 0\n-120 267 0\n-122 269 0\n-124 271 0\n-125 272 0\n-126 273 0\n-127 274 0\n-128 275 0\n-129 276 0\n-130 277 0\n-132 279 0\n-133 280 0\n-134 281 0\n-135 282 0\n-136 283 0\n-137 284 0\n-138 285 0\n-140 287 0\n-141 288 0\n-142 289 0\n-143 290 0\n-144 291 0\n-145 292 0\n-146 293 0\n-248 -264 250 0\n-248 -265 251 0\n-249 -271 250 0\n-249 -272 251 0\n-249 -273 252 0\n-250 -279 251 0\n-250 -280 252 0\n-251 -287 252 0\n-256 -267 253 0\n-256 -271 257 0\n-256 -272 258 0\n-256 -273 259 0\n-257 -274 253 0\n-257 -279 258 0\n-257 -280 259 0\n-258 -281 253 0\n-258 -287 259 0\n-259 -288 253 0\n-264 -275 261 0\n-264 -279 265 0\n-264 -280 266 0\n-265 -282 261 0\n-265 -287 266 0\n-266 -289 261 0\n-267 -248 269 0\n-271 -274 267 0\n-271 -276 269 0\n-271 -280 273 0\n-272 -281 267 0\n-272 -283 269 0\n-272 -287 273 0\n-273 -288 267 0\n-273 -290 269 0\n-274 -248 276 0\n-274 -249 277 0\n-275 -256 277 0\n-279 -281 274 0\n-279 -282 275 0\n-279 -284 277 0\n-279 -287 280 0\n-280 -288 274 0\n-280 -289 275 0\n-280 -290 276 0\n-280 -291 277 0\n-281 -249 284 0\n-281 -250 285 0\n-282 -256 284 0\n-282 -257 285 0\n-283 -264 285 0\n-284 -271 285 0\n-287 -288 281 0\n-287 -289 282 0\n-287 -290 283 0\n-287 -291 284 0\n-287 -292 285 0\n-288 -248 290 0\n-288 -249 291 0\n-288 -250 292 0\n-288 -251 293 0\n-289 -256 291 0\n-289 -257 292 0\n-289 -258 293 0\n-290 -264 292 0\n-290 -265 293 0\n-291 -271 292 0\n-291 -272 293 0\n-292 -279 293 0\n-154 0\n-203 0\n-252 0\n2 51 100 0\n-155 0\n-204 0\n-253 0\n10 59 108 0\n-163 0\n-212 0\n-261 0\n18 67 116 0\n-171 0\n-220 0\n-269 0\n26 75 124 0\n-179 0\n-228 0\n-277 0\n34 83 132 0\n-187 0\n-236 0\n-285 0\n42 91 140 0\n-195 0\n-244 0\n-293 0\n-2 -59 -113 0\n-2 -60 -120 0\n-2 -109 -71 0\n-2 -61 -127 0\n-2 -110 -78 0\n-2 -62 -134 0\n-2 -111 -85 0\n-2 -63 -141 0\n-2 -112 -92 0\n-52 -18 -120 0\n-101 -18 -71 0\n-3 -117 -78 0\n-52 -19 -127 0\n-52 -117 -29 0\n-101 -19 -78 0\n-101 -68 -29 0\n-3 -69 -134 0\n-52 -20 -134 0\n-101 -20 -85 0\n-101 -69 -36 0\n-3 -70 -141 0\n-3 -119 -92 0\n-52 -21 -141 0\n-4 -75 -127 0\n-4 -124 -78 0\n-53 -26 -127 0\n-53 -124 -29 0\n-102 -26 -78 0\n-102 -75 -29 0\n-4 -76 -134 0\n-4 -125 -85 0\n-53 -27 -134 0\n-53 -125 -36 0\n-102 -27 -85 0\n-102 -76 -36 0\n-4 -77 -141 0\n-4 -126 -92 0\n-53 -28 -141 0\n-102 -28 -92 0\n-5 -83 -134 0\n-5 -132 -85 0\n-54 -34 -134 0\n-54 -132 -36 0\n-103 -34 -85 0\n-103 -83 -36 0\n-5 -84 -141 0\n-5 -133 -92 0\n-54 -35 -141 0\n-103 -35 -92 0\n-6 -91 -141 0\n-6 -140 -92 0\n-55 -42 -141 0\n-104 -42 -92 0\n-10 -67 -121 0\n-59 -18 -121 0\n-59 -116 -23 0\n-10 -68 -128 0\n-10 -117 -79 0\n-59 -19 -128 0\n-59 -117 -30 0\n-10 -69 -135 0\n-10 -118 -86 0\n-59 -20 -135 0\n-59 -118 -37 0\n-10 -70 -142 0\n-10 -119 -93 0\n-59 -21 -142 0\n-59 -119 -44 0\n-11 -75 -128 0\n-11 -124 -79 0\n-60 -124 -30 0\n-109 -26 -79 0\n-109 -75 -30 0\n-11 -76 -135 0\n-60 -27 -135 0\n-60 -125 -37 0\n-109 -27 -86 0\n-109 -76 -37 0\n-11 -77 -142 0\n-11 -126 -93 0\n-60 -28 -142 0\n-60 -126 -44 0\n-109 -28 -93 0\n-109 -77 -44 0\n-12 -83 -135 0\n-12 -132 -86 0\n-61 -132 -37 0\n-110 -34 -86 0\n-110 -83 -37 0\n-12 -84 -142 0\n-12 -133 -93 0\n-61 -35 -142 0\n-61 -133 -44 0\n-110 -35 -93 0\n-110 -84 -44 0\n-13 -91 -142 0\n-13 -140 -93 0\n-62 -42 -142 0\n-62 -140 -44 0\n-111 -42 -93 0\n-111 -91 -44 0\n-18 -75 -129 0\n-18 -124 -80 0\n-67 -26 -129 0\n-67 -124 -31 0\n-18 -76 -136 0\n-18 -125 -87 0\n-67 -27 -136 0\n-67 -125 -38 0\n-18 -77 -143 0\n-18 -126 -94 0\n-67 -28 -143 0\n-67 -126 -45 0\n-19 -83 -136 0\n-19 -132 -87 0\n-68 -34 -136 0\n-68 -132 -38 0\n-117 -34 -87 0\n-117 -83 -38 0\n-19 -84 -143 0\n-19 -133 -94 0\n-68 -35 -143 0\n-68 -133 -45 0\n-117 -35 -94 0\n-117 -84 -45 0\n-20 -91 -143 0\n-20 -140 -94 0\n-69 -42 -143 0\n-69 -140 -45 0\n-118 -42 -94 0\n-118 -91 -45 0\n-26 -83 -137 0\n-26 -132 -88 0\n-75 -34 -137 0\n-75 -132 -39 0\n-124 -34 -88 0\n-124 -83 -39 0\n-26 -84 -144 0\n-26 -133 -95 0\n-75 -35 -144 0\n-75 -133 -46 0\n-124 -35 -95 0\n-124 -84 -46 0\n-27 -91 -144 0\n-27 -140 -95 0\n-76 -42 -144 0\n-76 -140 -46 0\n-125 -42 -95 0\n-125 -91 -46 0\n-34 -91 -145 0\n-34 -140 -96 0\n-83 -42 -145 0\n-83 -140 -47 0\n-132 -42 -96 0\n-132 -91 -47 0\n-2 -2 295 0\n-100 -100 0\n-295 -10 -10 296 0\n-295 -108 -108 0\n-296 -18 -18 297 0\n-296 -116 -116 0\n-297 -26 -26 298 0\n-297 -124 -124 0\n-298 -34 -34 299 0\n-298 -132 -132 0\n-299 -140 -140 0\n-51 -51 0\n-2 -59 337 0\n-337 -59 -67 0\n-2 -59 349 0\n-349 -59 -116 350 0\n-350 -116 -75 0\n-2 -18 361 0\n-361 -59 -26 0\n-2 -67 373 0\n-373 -10 -75 374 0\n-374 -67 -34 375 0\n-374 -67 -83 0\n-375 -75 -91 0\n-2 -116 379 0\n-379 -59 -26 380 0\n-379 -59 -124 0\n-380 -116 -132 0\n-2 -67 385 0\n-385 -10 -75 386 0\n-386 -67 -132 387 0\n-387 -75 -91 0\n-387 -75 -140 388 0\n-388 -132 -92 0\n-388 -132 -141 0\n-2 -26 397 0\n-397 -10 -34 398 0\n-397 -59 -34 0\n-397 -59 -83 398 0\n-398 -67 -42 0\n-398 -116 -42 0\n-2 -26 403 0\n-403 -59 -132 404 0\n-404 -116 -42 0\n-2 -75 409 0\n-409 -10 -83 410 0\n-409 -59 -83 0\n-410 -18 -91 411 0\n-411 -75 -92 0\n-2 -124 415 0\n-415 -10 -132 416 0\n-415 -59 -132 0\n-416 -67 -42 417 0\n-416 -67 -140 0\n-417 -124 -92 418 0\n-417 -124 -141 0\n-418 -132 -2 0\n-2 -75 421 0\n-421 -59 -132 422 0\n-422 -18 -91 423 0\n-423 -75 -141 424 0\n-424 -132 -2 425 0\n-425 -91 -59 0\n-2 -124 427 0\n-427 -10 -132 428 0\n-428 -67 -91 429 0\n-429 -124 -92 0\n-429 -124 -141 0\n-2 -34 433 0\n-433 -10 -42 434 0\n-433 -59 -42 0\n-433 -59 -91 434 0\n-434 -67 -92 435 0\n-434 -116 -141 435 0\n-435 -75 -2 0\n-435 -124 -2 0\n-2 -34 439 0\n-439 -10 -42 440 0\n-440 -67 -141 441 0\n-441 -75 -2 0\n-441 -124 -2 0\n-2 -83 445 0\n-445 -10 -91 446 0\n-445 -59 -91 0\n-446 -67 -92 0\n-2 -132 451 0\n-451 -10 -140 452 0\n-451 -59 -42 452 0\n-451 -59 -140 0\n-452 -18 -141 453 0\n-452 -67 -141 0\n-452 -116 -141 0\n-453 -75 -2 454 0\n-454 -132 -10 0\n-2 -83 457 0\n-457 -59 -140 458 0\n-458 -116 -92 0\n-2 -132 463 0\n-463 -59 -91 464 0\n-464 -116 -141 0\n-2 -42 469 0\n-469 -10 -43 470 0\n-469 -59 -92 470 0\n-470 -18 -2 471 0\n-470 -116 -2 0\n-471 -26 -10 472 0\n-471 -75 -59 472 0\n-472 -83 -18 0\n-472 -132 -18 0\n-2 -42 475 0\n-475 -59 -141 476 0\n-476 -18 -2 477 0\n-477 -124 -59 478 0\n-478 -83 -18 0\n-2 -91 481 0\n-481 -10 -92 482 0\n-481 -59 -92 0\n-482 -67 -2 483 0\n-483 -75 -10 484 0\n-483 -124 -10 0\n-484 -83 -67 0\n-484 -132 -67 0\n-2 -140 487 0\n-487 -10 -141 488 0\n-487 -59 -43 488 0\n-487 -59 -141 0\n-488 -67 -2 489 0\n-488 -116 -2 0\n-489 -124 -10 0\n-2 -43 505 0\n-505 -10 -2 506 0\n-505 -59 -2 0\n-506 -18 -10 507 0\n-506 -67 -10 0\n-507 -26 -18 508 0\n-507 -75 -18 0\n-508 -83 -26 0\n-2 -43 511 0\n-511 -10 -2 512 0\n-512 -18 -10 513 0\n-512 -67 -10 0\n-513 -75 -18 0\n-513 -124 -18 0\n-2 -92 517 0\n-517 -59 -2 518 0\n-518 -18 -59 519 0\n-518 -116 -10 0\n-518 -116 -59 0\n-519 -75 -18 520 0\n-519 -124 -18 0\n-519 -124 -67 0\n-520 -34 -75 521 0\n-521 -140 -34 0\n"
  "825 -7 0 490 139 0\n826 -56 0 491 269 0\n827 -105 0 492 391 0\n828 -16 0 498 146 0\n829 -65 0 499 276 0\n830 -114 0 500 396 0\n831 -24 0 502 153 0\n832 -73 0 503 283 0\n833 -122 0 504 401 0\n834 -32 0 506 160 0\n835 -81 0 507 290 0\n836 -130 0 508 408 0\n837 -40 0 510 167 0\n838 -89 0 511 297 0\n839 -138 0 512 415 0\n840 -48 0 514 174 0\n841 -97 0 515 304 0\n842 -146 0 516 422 0\n843 -2 295 0 672 0\n844 -100 0 673 0\n845 -295 -10 296 0 674 0\n846 -295 -108 0 675 0\n847 -296 -18 297 0 676 0\n848 -296 -116 0 677 0\n849 -297 -26 298 0 678 0\n850 -297 -124 0 679 0\n851 -298 -34 299 0 680 0\n852 -298 -132 0 681 0\n853 -299 -140 0 682 0\n854 -51 0 683 0\n855 2 0 854 844 493 0\n856 149 0 855 134 0\n857 295 0 855 843 0\n858 -161 0 856 490 178 0\n859 -162 0 856 498 199 0\n860 -108 0 857 846 0\n861 -14 0 858 144 0\n862 -15 0 859 145 0\n863 -59 337 0 855 684 0\n864 -59 349 0 855 686 0\n865 -18 361 0 855 689 0\n866 -67 373 0 855 691 0\n867 -116 379 0 855 696 0\n868 -67 385 0 855 700 0\n869 -26 397 0 855 707 0\n870 -26 403 0 855 713 0\n871 -75 409 0 855 716 0\n872 -124 415 0 855 721 0\n873 -418 -132 0 855 728 0\n874 -75 421 0 855 729 0\n875 -424 -132 425 0 855 733 0\n876 -124 427 0 855 735 0\n877 -34 433 0 855 740 0\n878 -435 -75 0 855 746 0\n879 -435 -124 0 855 747 0\n880 -34 439 0 855 748 0\n881 -441 -75 0 855 751 0\n882 -441 -124 0 855 752 0\n883 -83 445 0 855 753 0\n884 -132 451 0 855 757 0\n885 -453 -75 454 0 855 764 0\n886 -83 457 0 855 766 0\n887 -132 463 0 855 769 0\n888 -42 469 0 855 772 0\n889 -470 -18 471 0 855 775 0\n890 -470 -116 0 855 776 0\n891 -42 475 0 855 781 0\n892 -476 -18 477 0 855 783 0\n893 -91 481 0 855 786 0\n894 -482 -67 483 0 855 789 0\n895 -140 487 0 855 794 0\n896 -488 -67 489 0 855 798 0\n897 -488 -116 0 855 799 0\n898 -43 505 0 855 801 0\n899 -505 -10 506 0 855 802 0\n900 -505 -59 0 855 803 0\n901 -43 511 0 855 809 0\n902 -511 -10 512 0 855 810 0\n903 -92 517 0 855 815 0\n904 -517 -59 518 0 855 816 0\n905 -512 166 116 -10 0 812 501 147 811 813 814 202 505 154 0\n906 -124 116 -519 0 833 832 831 821 822 66 0\n907 -70 44 63 112 -10 0 499 861 280 581 337 63 300 0\n908 -119 44 63 112 -10 0 500 861 399 582 446 63 418 0\n909 -94 95 144 28 -18 46 0 503 301 627 349 107 286 0\n910 -76 119 70 -18 -34 -42 0 860 858 506 515 504 168 161 235 252 147 259 171 877 742 497 140 190 204 156 150 172 285 662 385 302 909 86 419 626 455 107 404 0\n911 -18 124 63 112 -34 -42 0 506 860 858 836 835 834 511 516 504 877 742 497 140 190 150 168 198 161 195 188 189 235 252 172 166 147 187 204 202 203 259 256 156 154 155 171 170 95 284 650 369 296 907 908 910 99 403 664 488 420 909 86 419 626 455 107 404 0\n912 -68 44 143 12 210 112 -10 178 -83 -42 0 510 515 858 499 861 512 516 274 908 907 140 229 158 190 150 291 386 303 668 168 253 173 198 143 278 573 331 382 288 355 301 294 86 171 639 238 162 122 292 322 360 272 300 41 63 393 605 418 614 470 484 412 394 54 0\n913 -45 -117 44 63 112 -67 46 96 -26 145 47 0 499 500 502 508 861 397 441 277 326 154 217 171 629 641 225 238 156 162 122 410 655 464 466 418 420 63 107 300 286 348 0\n914 44 143 12 19 210 112 -10 -67 -26 -83 -42 0 502 510 507 858 512 515 274 168 198 140 189 149 190 150 291 357 277 367 295 353 289 620 253 154 262 172 217 159 386 303 668 173 907 908 912 69 397 635 471 413 913 86 301 646 383 76 279 0\n915 -94 136 38 20 87 -42 0 515 301 646 383 76 279 0\n916 -133 128 79 -44 12 54 29 30 -92 0 492 855 496 410 563 609 429 41 389 393 521 435 11 405 0\n917 -117 35 -44 12 54 29 30 -92 -10 96 145 47 0 495 500 299 325 397 574 441 406 916 122 292 611 322 41 272 0\n918 -44 12 19 54 29 -92 177 80 -10 129 31 96 145 47 0 495 499 299 325 158 170 237 162 917 69 278 573 331 288 916 122 292 611 322 41 272 0\n919 -231 226 128 44 12 210 112 30 -83 -42 0 858 861 512 516 291 355 294 288 274 168 198 143 322 360 272 300 41 63 393 605 418 614 470 484 412 394 54 0\n920 -133 126 28 44 11 210 112 23 121 219 46 -26 0 508 861 274 282 410 655 466 420 107 286 319 348 271 300 35 63 392 418 482 0\n921 -117 118 69 20 87 -83 0 512 397 635 471 76 413 0\n922 159 19 -92 -10 -67 -26 -83 -42 0 510 507 858 855 856 502 495 515 504 516 499 291 386 299 376 267 325 154 217 140 175 227 157 525 229 158 168 198 189 149 214 152 570 357 277 367 295 353 289 326 620 253 262 172 159 303 668 173 142 191 141 918 914 419 644 628 455 486 404 398 920 921 69 278 573 638 331 122 919 292 0\n923 -133 126 28 44 210 112 23 121 219 46 -26 0 508 861 274 410 655 920 466 420 107 286 595 348 63 300 0\n924 -143 44 35 19 210 112 -10 -67 -26 -83 -42 0 515 510 507 858 502 504 516 499 861 274 154 217 140 229 158 168 198 189 149 214 152 570 291 357 277 367 295 353 289 326 620 253 262 172 159 386 303 668 173 419 644 628 455 486 404 398 921 69 278 573 331 923 122 292 360 919 300 606 63 0\n925 -84 -12 143 119 70 44 19 63 112 21 227 129 31 0 861 499 289 292 606 361 63 301 300 86 337 641 333 69 278 0\n926 19 -92 -10 -67 -26 -83 -42 0 515 502 507 855 495 858 510 861 500 516 499 299 325 274 525 140 190 150 277 353 289 620 154 217 159 291 386 303 668 168 253 173 198 143 922 196 246 257 162 164 170 907 908 924 914 601 925 122 410 607 63 418 614 446 484 443 394 397 54 69 294 278 355 331 0\n927 -133 126 77 28 46 -26 0 508 410 655 466 107 420 0\n928 -143 -18 46 96 -26 145 47 0 860 858 504 507 154 147 202 865 690 497 140 190 208 162 204 156 419 626 455 404 927 122 292 654 362 107 302 0\n929 -18 193 -26 145 -83 47 141 -469 0 515 860 858 827 826 825 855 495 503 507 172 154 291 386 303 147 865 779 202 259 690 171 497 140 777 190 255 889 150 204 208 170 773 156 162 31 299 525 325 274 907 908 928 86 301 627 349 286 927 122 292 654 362 909 302 0\n930 -116 -518 0 828 829 860 830 818 819 34 0\n931 -94 38 87 80 129 31 -83 20 -42 0 515 291 386 301 646 915 382 84 630 278 921 69 0\n932 291 11 -289 53 4 72 -288 121 -157 0 856 502 855 495 175 213 151 214 152 479 482 388 392 35 271 518 316 6 281 0\n933 -60 54 5 53 4 -76 104 55 29 -26 22 6 0 855 495 508 512 285 271 518 316 281 344 6 293 388 544 551 22 457 411 405 468 11 389 0\n934 -76 86 79 35 128 126 28 44 219 -141 121 -26 145 -230 -157 -42 0 490 858 856 502 510 515 861 516 491 855 496 508 495 512 417 481 390 440 395 282 568 524 168 253 154 262 172 214 216 158 175 213 215 157 386 303 151 152 173 198 143 186 138 285 662 385 302 107 286 552 309 348 266 300 63 418 614 595 484 394 932 466 410 122 292 562 606 311 267 933 35 392 519 594 431 54 400 412 6 470 388 544 551 393 457 41 405 272 11 320 389 354 468 293 411 22 0\n935 -27 118 69 87 -67 20 0 502 155 624 222 76 165 0\n936 -125 118 69 87 -67 20 0 504 403 625 452 76 413 0\n937 -68 -76 28 -143 44 219 -141 121 -26 145 -230 -10 -42 0 504 499 285 345 294 419 455 404 140 278 573 638 331 934 288 0\n938 -143 44 -141 -67 -26 -83 -10 -42 0 858 502 499 507 516 510 291 357 277 367 295 353 289 326 620 570 154 249 166 217 159 648 296 668 168 198 140 189 149 419 644 628 486 398 921 935 936 99 937 69 148 630 248 76 165 0\n939 -76 143 44 -141 -67 -26 145 -230 -10 -42 0 858 510 507 855 496 515 502 499 417 440 395 524 907 908 277 353 289 326 620 570 168 253 154 262 172 217 159 386 303 140 190 150 173 285 385 345 381 294 301 86 171 629 913 225 260 238 156 148 162 69 278 573 331 934 288 0\n940 -68 76 143 70 119 44 -141 121 -67 137 88 -26 243 145 -157 -42 0 858 510 855 496 499 502 516 861 491 417 440 395 277 326 282 524 168 253 154 262 172 249 166 217 303 190 150 173 278 331 382 301 86 171 629 639 225 238 156 223 162 155 122 99 292 654 403 664 360 107 488 300 286 552 63 309 418 595 266 932 0\n941 -45 68 44 112 63 -67 96 -26 145 194 0 502 507 277 353 289 620 154 262 172 217 159 173 171 913 260 69 148 0\n942 44 -141 -67 -26 -83 -10 -42 0 858 515 502 510 855 507 496 417 440 395 291 357 277 367 295 353 289 524 620 570 154 249 166 217 159 648 386 303 296 668 168 198 140 189 149 190 150 253 908 907 938 939 940 941 86 646 931 80 625 935 99 0\n943 -133 128 79 12 -44 259 30 0 410 609 437 41 393 0\n944 -117 35 12 -44 55 -141 30 29 145 -83 -10 47 6 0 515 496 516 500 491 855 495 512 417 481 390 440 291 386 303 397 574 441 406 943 122 292 562 611 311 41 267 272 520 320 287 354 11 293 389 561 22 468 411 0\n945 -441 26 0 881 882 505 0\n946 -67 43 -34 -10 -42 0 827 826 825 880 749 877 741 711 708 869 945 750 31 744 878 879 505 0\n947 -92 124 -18 -34 -42 0 855 495 299 525 325 911 274 0\n948 -136 27 88 137 -18 39 0 504 413 622 452 99 403 0\n949 -111 36 104 6 55 0 855 496 394 523 438 22 411 0\n950 -87 27 88 137 -18 39 0 503 295 623 346 99 285 0\n951 -62 36 104 6 55 0 855 495 273 522 323 22 293 0\n952 -118 13 62 111 37 -10 0 500 398 578 444 54 412 0\n953 13 136 20 87 62 111 37 -10 38 0 499 952 76 279 577 335 54 294 0\n954 136 20 87 227 129 19 62 111 37 30 -10 -141 38 31 145 -91 47 0 511 855 496 858 514 861 499 516 500 289 140 190 150 417 440 395 524 298 374 303 953 143 612 258 170 908 907 63 300 337 379 336 272 279 76 398 647 486 419 86 301 382 361 278 292 69 397 574 640 441 122 406 410 607 41 437 393 0\n955 -136 80 129 19 31 -34 0 512 413 632 471 69 397 0\n956 -94 -75 19 28 -18 243 145 47 0 506 503 508 284 384 302 341 289 618 147 231 159 303 301 382 361 278 292 69 640 122 410 657 466 909 420 0\n957 -20 94 -10 -141 -91 0 855 496 858 514 140 190 150 417 440 395 524 149 642 189 261 258 171 170 908 907 86 0\n958 166 -10 124 -141 -18 -91 -34 0 514 858 856 506 516 491 836 835 834 503 511 298 312 268 566 417 481 390 161 235 147 247 140 175 241 163 951 949 190 204 156 244 164 231 229 158 165 159 374 666 264 173 148 202 154 95 284 618 341 289 955 956 957 954 295 634 368 69 278 0\n959 19 -75 -10 -141 -18 -91 -34 0 514 858 856 506 516 491 503 511 284 341 289 618 298 312 268 566 417 481 390 161 235 147 247 140 175 241 163 951 949 190 204 156 244 164 231 229 158 165 159 374 666 264 173 956 955 957 954 295 634 368 69 278 0\n960 -143 -19 95 -75 35 28 -18 96 145 47 0 504 508 419 626 636 455 122 404 410 657 466 107 420 0\n961 -75 70 119 35 45 -10 -141 -18 -91 -34 0 514 511 858 503 147 140 190 204 156 150 298 374 303 666 161 264 173 284 341 384 302 959 960 86 301 637 361 122 292 0\n962 -10 124 -141 -18 -91 -34 0 514 511 855 496 858 503 507 417 440 395 524 147 298 374 303 666 161 264 173 140 190 150 204 156 958 260 208 171 255 162 170 908 907 961 505 154 262 172 928 86 301 627 349 286 927 122 292 654 362 909 302 0\n963 28 -94 -75 -18 243 145 47 0 503 506 284 341 301 361 292 384 302 303 956 637 122 162 656 239 909 172 0\n964 -280 30 29 128 12 5 54 79 259 0 492 855 495 429 437 389 393 41 272 520 320 11 287 0\n965 -61 -35 44 -141 243 0 855 496 861 417 440 395 524 272 608 379 63 300 0\n966 -35 44 -94 79 80 129 -59 -141 31 -91 -34 0 491 855 496 516 511 858 859 498 512 861 298 374 301 382 278 417 481 390 440 395 566 524 312 268 161 162 640 196 69 142 148 575 205 206 232 158 233 163 164 949 951 965 41 393 604 610 470 63 412 612 54 0\n967 -94 124 -141 -18 -91 -34 0 514 511 498 859 506 855 495 834 835 836 828 829 860 830 490 492 508 862 503 962 34 270 339 865 690 95 284 340 288 341 289 618 313 275 517 417 147 231 159 200 151 201 298 374 303 666 161 264 173 301 382 361 278 292 963 156 554 184 224 136 179 170 135 966 122 410 637 429 466 69 479 397 388 423 387 1 265 526 338 6 281 0\n968 -36 118 -101 87 136 38 0 859 163 536 209 76 149 0\n969 -101 134 87 136 211 251 6 38 55 0 390 387 424 398 968 22 293 535 334 76 279 0\n970 -79 257 26 -434 -59 -141 0 503 507 498 270 339 282 863 685 288 352 340 271 284 505 402 879 586 432 745 392 501 147 571 201 35 152 0\n971 -116 26 -59 0 836 835 834 864 867 687 698 688 95 0\n972 -133 44 -12 275 -141 0 855 496 861 417 440 395 524 410 607 464 63 418 0\n973 -132 -91 -141 -59 0 836 835 834 734 863 685 887 723 875 770 872 771 501 865 690 95 874 732 730 731 0\n974 -12 93 -84 194 -141 0 855 496 861 417 440 395 524 142 606 257 63 170 0\n975 -159 111 13 135 86 55 6 104 0 856 510 177 246 243 164 163 54 951 0\n976 -67 216 87 118 27 88 137 20 39 0 279 277 936 328 99 285 0\n977 -116 26 0 857 860 848 971 845 497 0\n978 -10 92 91 -67 -124 -34 0 827 826 825 842 841 840 800 805 896 899 898 31 946 795 132 895 0\n979 92 91 -34 -67 -124 0 828 829 860 830 978 34 863 685 0\n980 -26 -177 -34 0 502 860 154 869 217 709 229 497 140 0\n981 -87 129 31 80 19 -34 0 511 295 634 368 278 69 0\n982 -13 142 63 112 -140 0 514 861 143 613 258 63 170 0\n983 -59 -67 0 863 685 0\n984 -109 4 102 53 22 0 855 496 392 519 431 6 400 0\n985 186 102 53 -183 -67 0 499 860 502 856 855 495 240 983 497 140 175 213 151 214 152 570 277 326 282 242 245 136 141 984 35 271 518 316 6 281 0\n986 151 109 102 53 -67 0 499 860 502 856 855 495 983 497 140 175 213 151 214 152 570 277 326 282 136 176 141 35 271 518 316 6 281 0\n987 -78 79 128 30 12 0 855 495 287 521 320 41 272 0\n988 -103 251 34 -36 0 839 838 837 389 561 428 118 409 0\n989 -54 202 34 -36 0 267 559 310 509 291 0\n990 -103 210 91 -132 226 142 128 30 43 34 -36 0 856 516 492 827 826 825 842 841 840 855 510 861 274 409 489 421 288 163 240 246 142 389 988 429 480 430 410 417 416 31 132 525 565 168 670 253 173 122 292 322 360 272 300 41 63 611 0\n991 -127 79 128 30 12 0 855 496 405 520 435 41 393 0\n992 91 226 135 79 128 -103 30 86 43 34 -36 0 494 856 510 492 837 838 839 825 826 827 495 842 841 840 516 988 481 417 31 299 325 561 118 409 489 430 416 163 240 246 142 197 143 990 132 418 614 484 483 394 393 54 41 603 0\n993 -483 484 -10 26 0 790 791 505 0\n994 -124 -42 -92 -132 -67 0 860 873 983 497 872 726 722 724 0\n995 79 128 226 91 -103 30 86 43 34 -36 0 856 510 840 841 842 837 838 839 492 516 825 826 827 495 512 988 481 417 31 299 325 565 389 429 410 561 118 409 489 421 430 416 132 670 168 253 173 122 292 322 272 163 240 246 142 41 393 992 470 412 0\n996 -79 -11 219 26 0 836 835 834 288 586 340 95 284 0\n997 -124 -18 116 34 0 857 830 860 829 828 827 826 825 842 841 840 850 872 906 847 845 34 900 817 723 898 904 509 903 883 785 31 755 784 797 892 895 782 132 891 0\n998 -132 91 43 -10 177 86 79 128 30 78 227 129 31 176 -36 0 858 856 516 492 499 827 826 825 842 841 840 855 495 510 163 240 246 140 188 148 190 150 142 991 289 232 161 157 243 137 409 559 489 11 421 389 988 995 429 480 430 331 410 417 416 278 31 132 69 299 525 565 168 670 397 325 253 485 274 173 419 918 122 908 907 292 641 361 86 301 0\n999 47 145 -117 35 -141 84 -83 -10 79 128 30 29 -36 0 856 510 515 855 496 500 861 397 441 417 440 395 524 291 386 303 163 240 246 142 26 23 122 944 410 437 464 393 418 41 63 272 300 379 0\n1000 -47 -83 91 0 510 842 841 840 173 669 253 132 168 0\n1001 -145 -83 91 0 512 421 668 477 513 416 0\n1002 -96 140 -132 0 511 303 670 374 513 298 0\n1003 -47 140 -132 0 510 842 841 840 173 671 253 132 168 0\n1004 -18 26 117 68 34 19 116 0 506 836 835 834 503 147 997 231 95 159 284 618 341 69 289 0\n1005 26 -42 117 215 -92 -132 34 19 116 0 833 832 831 836 835 834 278 1004 66 277 994 327 95 284 0\n1006 -26 117 68 298 19 -296 0 502 833 832 831 507 848 154 849 217 847 159 66 277 620 353 69 289 0\n1007 117 215 140 -92 -132 34 19 -10 0 857 833 832 831 278 852 845 848 1006 1004 1005 66 513 793 893 993 787 894 0\n1008 -92 -132 -124 -67 0 860 872 983 497 722 725 876 736 738 994 737 513 0\n1009 -132 -124 -67 0 860 827 826 825 876 872 983 497 805 899 898 722 736 725 1008 31 727 739 724 737 513 0\n1010 102 151 53 -67 0 860 856 502 136 983 497 140 175 213 151 986 984 0\n1011 -144 76 -91 88 39 137 0 516 420 660 488 99 403 0\n1012 -36 78 127 29 54 251 34 0 510 163 988 243 11 137 0\n1013 -158 12 13 111 20 54 55 6 251 87 38 -83 79 -10 -264 34 0 500 856 506 495 512 390 291 471 413 441 406 176 230 228 158 157 991 987 1012 951 953 605 41 272 320 354 293 22 411 556 468 11 389 0\n1014 -37 11 28 76 77 95 -91 259 88 39 137 -67 0 499 860 502 1011 983 497 140 214 152 570 277 326 282 164 221 155 99 665 592 107 35 404 392 434 0\n1015 217 -91 -141 39 38 -83 137 79 -67 -264 34 0 512 499 856 858 502 855 496 491 507 860 500 516 514 983 497 277 353 291 356 298 372 301 957 312 310 267 357 373 302 268 566 417 481 390 440 395 524 295 296 140 214 152 190 150 175 213 570 326 282 471 413 280 329 336 286 347 279 285 76 398 578 647 444 486 412 419 86 908 170 617 258 224 143 156 975 142 1011 1013 141 1014 54 951 163 220 155 99 665 107 404 598 434 35 392 0\n1016 -126 11 94 -141 -67 0 499 858 860 502 855 496 504 417 440 395 524 983 497 140 214 152 190 150 570 277 326 282 404 629 455 434 419 392 35 598 908 907 86 0\n1017 -102 27 -36 251 88 39 137 0 388 551 426 99 403 0\n1018 -128 19 129 31 80 -10 0 500 406 573 441 69 397 0\n1019 -29 102 -124 -67 0 506 157 543 228 1010 0\n1020 -54 -83 133 43 0 515 491 827 826 825 291 386 303 267 311 376 292 358 299 298 31 1000 1001 564 122 0\n1021 -110 27 62 111 20 13 137 39 -67 -83 0 860 507 512 499 291 357 277 367 295 983 497 296 393 605 470 952 412 976 54 335 294 0\n1022 -11 110 61 128 26 219 12 0 506 141 996 230 41 158 0\n1023 -46 125 -140 39 137 88 0 514 172 663 263 99 155 0\n1024 -77 291 -289 -141 -157 -60 0 491 417 40 38 36 286 552 309 932 266 0\n1025 -83 231 103 78 127 29 43 133 0 515 490 292 291 1020 386 358 11 303 298 137 1000 1001 185 122 162 0\n1026 -194 91 83 -10 -141 -26 0 857 510 514 839 838 837 833 832 831 845 848 253 264 168 161 513 118 852 884 849 758 847 762 66 0\n1027 -292 182 91 83 0 512 516 842 841 840 477 489 416 409 132 509 168 161 236 0\n1028 -34 -42 43 0 860 857 827 826 825 855 496 877 742 497 845 946 848 501 847 850 947 31 417 524 440 911 395 0\n1029 -181 87 136 178 20 -10 62 111 13 0 140 229 234 233 165 164 953 0\n1030 -117 70 119 45 21 -35 292 0 397 640 485 86 419 0\n1031 -18 -10 63 112 -35 -132 34 -42 0 516 508 506 857 858 511 162 196 140 188 148 168 198 189 149 190 150 845 848 239 409 461 414 489 852 147 997 847 203 187 259 849 155 256 171 505 170 284 651 908 907 369 296 948 950 1030 1004 633 638 915 86 0\n1032 -88 124 -132 0 511 296 649 369 505 284 0\n1033 -39 124 -132 0 510 836 835 834 166 651 249 95 154 0\n1034 -94 27 87 39 88 -67 20 137 -42 0 515 301 646 383 976 0\n1035 -77 -75 79 44 219 121 23 110 210 112 -35 0 858 861 508 282 274 162 196 142 286 319 348 271 300 63 595 608 35 392 589 458 41 406 0\n1036 -95 27 39 88 137 -42 0 515 302 664 385 99 285 0\n1037 -144 27 39 88 137 -42 0 516 420 662 488 99 403 0\n1038 -126 94 70 119 -67 21 0 504 404 629 455 86 419 0\n1039 -28 94 70 119 -67 21 0 502 156 628 225 86 171 0\n1040 -77 79 44 124 121 -67 23 110 102 210 112 -35 0 490 499 491 836 835 834 277 326 162 185 286 1035 309 95 266 154 1010 182 0\n1041 -27 -67 102 -134 153 0 155 548 183 1010 0\n1042 -215 70 119 44 27 39 88 124 121 -67 20 23 21 110 102 210 112 -35 137 -42 0 506 499 511 1037 1036 162 239 172 331 368 288 295 1040 1034 1038 1039 107 0\n1043 44 27 -10 110 102 -92 -35 -132 34 -42 140 0 510 508 516 506 502 858 495 855 831 832 857 833 836 835 834 845 848 525 299 325 274 1031 66 1009 1033 1032 570 277 162 196 140 188 148 168 198 189 149 214 152 190 150 239 172 409 489 421 461 414 670 253 173 908 907 1042 1007 327 1030 284 913 95 0\n1044 -77 11 -44 72 121 23 210 0 286 600 319 35 271 0\n1045 -10 -134 -92 -35 -132 34 -42 140 0 490 506 855 515 495 508 496 857 856 502 833 832 831 499 409 411 438 436 393 461 467 388 299 325 274 377 525 162 239 172 414 168 186 140 845 175 214 848 213 152 151 1031 66 277 570 1009 326 282 1032 1033 1041 1036 1037 1043 170 224 256 156 141 1044 107 553 598 35 392 984 433 266 403 308 99 285 0\n1046 140 84 43 103 78 29 127 91 83 133 0 842 841 840 510 839 838 837 516 490 511 827 826 825 515 830 860 829 828 132 168 888 186 253 138 173 1028 118 409 670 489 421 122 162 185 137 11 267 559 564 364 31 293 299 569 377 268 22 1045 34 983 774 723 890 872 501 865 780 889 690 778 505 0\n1047 -59 67 -140 43 83 0 827 826 825 895 797 760 31 884 903 509 904 824 709 930 869 501 817 906 505 823 820 0\n1048 -34 176 -140 84 43 103 78 29 127 133 0 492 512 514 490 511 827 826 825 515 416 477 421 430 390 161 667 264 232 173 163 122 162 185 137 11 267 558 564 364 31 293 299 567 22 377 268 0\n1049 -117 128 12 110 111 62 63 112 -132 30 -10 -140 0 500 511 416 409 462 397 574 441 41 460 464 272 603 412 418 366 982 294 54 0\n1050 -27 63 112 144 137 39 88 -18 -10 -140 0 858 514 504 140 190 147 204 156 187 150 102 155 661 1023 263 909 259 256 171 170 908 907 86 419 626 455 107 404 0\n1051 -143 27 144 137 39 88 28 -18 -140 0 504 515 416 419 626 455 404 453 403 1023 99 107 285 302 385 0\n1052 -45 87 37 38 111 62 136 63 112 -10 -140 0 514 500 416 171 645 261 149 953 76 982 398 418 445 446 0\n1053 -70 87 37 38 111 62 136 63 112 -10 -140 0 514 140 581 907 982 170 953 258 149 189 0\n1054 -68 20 13 -134 87 136 55 6 -132 30 -10 104 0 855 496 499 409 411 438 436 393 28 949 522 278 633 573 331 953 288 59 61 603 975 41 142 0\n1055 159 68 110 111 62 63 112 -132 34 -18 -10 -140 0 506 857 503 845 847 850 852 849 505 284 341 289 618 140 147 231 229 158 159 848 142 188 148 1018 1004 1049 0\n1056 -44 -134 55 63 6 112 -132 34 -18 -10 -140 0 506 503 508 857 855 492 496 514 510 500 409 411 438 436 393 416 430 390 28 949 522 845 847 850 1033 461 414 1032 476 420 1050 950 948 852 849 505 284 341 289 618 140 147 231 229 158 159 848 65 170 982 258 189 149 1054 1055 246 164 953 165 248 148 1018 1004 397 1049 441 602 460 54 412 0\n1057 19 13 68 110 111 62 63 112 -132 34 -18 -10 -140 0 506 857 503 510 500 1055 246 164 845 847 850 852 849 505 284 341 289 618 409 140 147 231 229 158 159 848 1018 1004 397 1049 441 602 460 54 412 0\n1058 13 68 70 119 110 111 62 63 112 -132 34 -18 -10 -140 0 858 508 857 510 1055 246 164 845 847 850 1033 409 461 414 1032 416 476 420 1050 950 140 190 147 204 156 1051 948 150 1057 148 248 165 953 1052 643 86 0\n1059 68 70 119 110 111 62 63 112 -132 34 -18 -10 -140 0 858 508 857 500 510 515 845 847 850 1033 409 461 414 1032 416 476 420 1050 950 140 190 147 204 156 1051 948 852 849 462 150 848 1055 246 164 1058 982 418 446 443 445 397 398 1004 148 248 165 1052 86 301 643 383 76 279 0\n1060 -13 38 70 119 111 62 87 143 136 63 112 -10 -140 0 858 500 515 140 190 150 416 55 982 1052 418 86 446 301 643 445 383 398 279 76 0\n1061 -134 55 63 6 112 -132 34 -18 -10 -140 0 492 506 858 508 857 855 496 514 845 847 850 1033 409 461 414 1032 416 476 420 1050 950 140 190 147 204 156 1051 948 231 229 158 150 430 390 28 411 522 949 438 436 393 1056 908 907 1059 633 1060 1054 149 643 261 86 171 0\n1062 -85 -132 103 78 29 127 0 511 293 557 364 11 267 0\n1063 67 -140 84 43 103 78 29 127 83 133 0 492 860 857 856 506 839 838 837 827 826 825 855 495 515 416 430 390 1047 497 140 845 175 848 501 147 847 231 850 227 1048 118 852 884 765 849 758 505 885 761 31 299 525 567 325 377 274 268 1061 1062 22 559 1012 0\n1064 -36 -132 251 78 29 127 0 120 559 1012 0\n1065 -75 388 -132 -67 -140 0 860 983 497 868 701 704 702 0\n1066 -77 109 -142 210 -67 0 499 860 502 983 497 140 214 152 570 277 326 282 286 595 319 35 271 0\n1067 -95 125 137 39 88 -140 0 515 302 661 385 99 285 0\n1068 -94 -13 87 38 62 111 63 112 137 39 88 -67 -140 0 860 500 515 416 982 418 446 445 398 983 497 65 908 581 93 301 643 1060 383 624 976 0\n1069 125 126 77 28 144 137 39 88 -140 0 1023 1067 107 0\n1070 283 94 70 119 87 37 38 62 111 63 112 -10 -140 0 858 140 190 150 416 413 475 1052 419 86 0\n1071 142 136 93 87 37 38 62 111 63 112 -10 -140 0 861 514 140 63 982 170 953 258 149 189 0\n1072 -142 -77 210 291 -67 0 418 1066 482 392 0\n1073 125 126 87 37 38 28 -159 62 111 55 210 6 112 291 137 39 88 -67 -140 0 492 860 502 861 499 274 420 983 497 140 214 152 570 277 326 282 416 430 390 1069 286 348 300 1072 63 982 1071 1044 952 79 624 976 99 335 590 294 975 0\n1074 -94 136 87 37 38 62 111 63 112 137 39 88 -67 -140 0 860 983 497 643 1068 953 0\n1075 283 87 37 38 62 111 63 112 137 39 88 -67 -140 0 860 858 983 497 140 190 150 416 413 475 1052 419 1074 1053 86 582 908 1071 65 0\n1076 136 -126 87 37 38 62 111 63 112 137 39 88 -67 -140 0 860 858 983 497 140 190 150 1053 1074 1038 582 908 1071 65 0\n1077 87 209 37 38 28 -159 102 62 111 -92 291 137 39 88 -67 -140 0 492 858 860 856 502 855 495 504 499 515 299 377 268 325 274 567 525 983 497 140 175 213 151 214 152 190 150 570 277 326 282 416 430 390 1075 452 403 1073 553 1076 79 85 624 976 99 335 383 285 294 301 308 318 266 271 984 35 590 975 982 65 581 908 1038 0\n1078 -87 -159 30 31 129 110 62 111 55 63 6 112 -132 80 -10 -140 0 492 511 500 416 409 462 430 390 295 631 368 1018 278 69 397 1049 441 602 460 464 412 418 975 982 0\n1079 142 109 86 -76 -126 93 37 62 111 63 112 23 121 72 -140 0 861 982 63 54 598 590 35 0\n1080 -126 38 37 -142 87 62 111 63 112 137 39 88 -67 -140 0 858 860 500 515 416 418 446 445 398 983 497 65 908 581 140 190 150 1076 1038 79 624 301 976 383 0\n1081 -28 109 -142 -67 0 499 860 502 858 983 497 140 214 152 570 277 326 282 156 597 193 35 141 0\n1082 38 -159 -142 87 62 111 55 210 6 112 291 137 39 88 -67 -140 0 510 504 246 164 418 482 392 1081 274 1075 1080 452 1073 403 0\n1083 -38 117 31 129 -132 80 0 510 165 633 248 69 148 0\n1084 -142 87 30 31 129 110 62 111 55 210 6 112 -132 -67 -140 0 507 860 508 500 499 504 274 416 409 461 476 420 414 1009 1033 1032 462 983 497 140 277 353 289 418 1072 446 482 443 392 397 1081 1083 1082 142 188 148 1018 69 278 331 288 41 603 1075 1080 452 1069 403 0\n1085 159 13 87 129 -173 -134 62 111 63 202 112 -132 -67 -140 0 507 856 508 496 860 502 499 511 504 855 495 983 497 140 214 216 158 217 159 409 411 438 436 393 461 467 388 414 1009 1033 1032 175 213 151 152 570 277 353 289 326 282 142 188 191 148 141 1018 1049 1083 69 278 331 288 41 272 603 366 1075 294 452 54 403 412 469 392 35 271 518 591 316 99 281 285 546 308 6 266 0\n1086 -60 -135 125 102 -134 202 137 39 88 22 0 855 495 271 518 591 316 99 281 285 546 308 6 266 0\n1087 -86 79 128 30 110 -132 0 511 294 602 366 41 272 0\n1088 -135 38 -159 87 -134 62 111 202 210 6 112 39 88 284 -67 -140 0 499 860 856 502 510 504 858 414 274 246 164 1075 452 403 411 467 388 268 416 476 983 497 140 175 213 151 214 152 570 277 326 282 412 1086 469 392 35 141 590 193 99 156 624 1073 1076 0\n1089 38 -159 13 87 -134 62 111 202 210 6 112 39 88 284 -67 -140 0 492 499 510 504 490 246 164 411 467 388 268 274 416 476 414 277 326 430 390 1075 452 403 1088 975 294 345 285 99 624 548 1076 1010 1073 184 156 0\n1090 87 129 -173 -134 62 111 202 210 6 112 -132 -67 -140 0 507 508 496 860 502 510 500 983 497 140 214 216 158 217 159 409 411 438 436 393 268 274 1009 1033 1032 461 277 353 289 1084 982 1085 246 164 1089 1083 71 397 574 1018 441 1087 460 54 412 0\n1091 -132 -67 -140 43 103 78 29 127 0 492 507 860 827 826 825 855 495 515 496 836 835 834 502 511 983 497 140 214 277 353 289 416 430 390 409 884 1062 1009 758 762 31 299 525 567 705 325 377 274 268 1064 949 951 22 411 438 436 393 1065 95 154 620 217 216 159 158 1090 295 631 1078 368 1018 142 278 1049 69 0\n1092 -87 26 19 -34 -67 0 507 511 836 835 834 504 277 353 289 295 368 327 284 95 402 621 449 981 407 0\n1093 -75 -36 202 151 -34 -67 251 0 506 860 856 502 511 983 497 140 175 213 163 220 155 161 235 166 284 650 369 296 1017 1010 266 549 308 99 285 0\n1094 84 43 133 103 78 29 127 91 83 0 512 834 835 836 515 825 826 827 511 490 506 856 514 502 860 492 1046 416 430 477 390 421 1063 983 497 140 175 213 1091 509 161 667 1048 235 264 226 228 166 173 980 122 162 185 137 11 267 558 564 364 31 293 299 567 377 268 22 163 220 155 1093 95 402 652 472 414 1017 1010 266 549 308 99 285 0\n1095 -109 86 -76 291 284 62 111 -140 -92 0 855 495 299 325 274 525 392 594 469 482 412 418 54 982 0\n1096 -76 125 209 291 284 88 94 -67 62 111 -140 186 -92 0 855 495 499 858 860 502 420 414 983 497 140 214 152 190 150 570 277 326 282 166 299 325 274 525 285 345 318 294 271 1095 35 141 590 245 164 54 982 65 581 1072 908 1038 1081 1069 0\n1097 -142 28 125 137 291 88 94 -67 39 -140 -92 0 855 495 860 858 420 983 497 140 190 150 299 325 274 525 65 581 1072 908 1069 1038 0\n1098 44 142 28 125 144 137 88 94 -67 39 -140 -92 0 855 495 499 860 858 861 983 497 140 190 150 277 326 299 325 274 525 908 907 63 1038 300 1069 348 286 0\n1099 125 -85 291 284 88 26 94 -67 62 111 -140 -34 53 -92 0 855 514 506 860 495 502 490 293 323 420 414 983 497 140 214 161 235 166 264 299 325 274 525 1096 99 155 624 550 221 222 1010 164 165 184 156 1097 1098 64 170 1071 255 1092 260 148 0\n1100 113 101 3 64 52 0 862 1 0\n1101 141 92 43 0 825 826 827 31 0\n1102 10 59 0 828 829 860 830 34 0\n1103 44 93 63 112 142 0 861 63 0\n1104 18 116 67 0 831 832 833 66 0\n1105 75 124 26 0 834 835 836 95 0\n1106 132 34 83 0 837 838 839 118 0\n1107 42 140 91 0 840 841 842 132 0\n1108 -157 150 0 856 175 0\n1109 -159 152 0 856 177 0\n1110 -150 -168 0 490 181 0\n1111 -151 -175 0 490 184 0\n1112 -152 -182 0 490 185 0\n1113 -153 -189 0 490 186 0\n1114 -157 -168 0 858 190 0\n1115 -158 -175 0 858 193 0\n1116 -159 -176 0 494 194 0\n1117 -159 -182 0 858 196 0\n1118 -160 -183 0 494 197 0\n1119 -160 -189 0 858 198 0\n1120 -165 -169 0 859 200 0\n1121 -165 -170 0 498 201 0\n1122 -166 -176 0 859 205 0\n1123 -166 -177 0 498 206 0\n1124 -167 -183 0 859 209 0\n1125 -167 -184 0 498 210 0\n1126 -168 -191 0 498 212 0\n1127 -169 -150 0 502 213 0\n1128 -170 -157 0 502 214 0\n1129 -173 -178 0 502 217 0\n1130 -174 -185 0 502 222 0\n1131 -175 -192 0 502 225 0\n1132 -176 177 0 856 226 0\n1133 -176 -151 0 506 228 0\n1134 -177 -158 0 506 230 0\n1135 -178 -165 0 506 231 0\n1136 -181 -186 0 506 235 0\n1137 -182 -193 0 506 239 0\n1138 -183 184 0 856 240 0\n1139 -183 -152 0 510 243 0\n1140 -184 -159 0 510 246 0\n1141 -185 -166 0 510 248 0\n1142 -186 -173 0 510 249 0\n1143 -189 -194 0 510 253 0\n1144 -190 191 0 856 254 0\n1145 -191 -160 0 514 258 0\n1146 -192 -167 0 514 261 0\n1147 -193 -174 0 514 263 0\n1148 -194 -181 0 514 264 0\n1149 -199 -217 0 491 306 0\n1150 -200 -224 0 491 309 0\n1151 -201 -231 0 491 311 0\n1152 -202 -238 0 491 312 0\n1153 -206 -211 0 495 313 0\n1154 -207 -218 0 495 316 0\n1155 -208 -225 0 495 320 0\n1156 -209 -232 0 495 323 0\n1157 -210 -239 0 495 325 0\n1158 -214 -219 0 499 326 0\n1159 -215 -226 0 499 331 0\n1160 -216 -233 0 499 335 0\n1161 -217 -240 0 499 337 0\n1162 -218 -199 0 503 338 0\n1163 -219 -206 0 503 339 0\n1164 -222 -227 0 503 341 0\n1165 -223 -234 0 503 346 0\n1166 -224 -241 0 503 349 0\n1167 -225 -200 0 507 350 0\n1168 -226 -207 0 507 352 0\n1169 -227 -214 0 507 353 0\n1170 -230 -235 0 507 357 0\n1171 -231 -242 0 507 362 0\n1172 -232 -201 0 511 364 0\n1173 -233 -208 0 511 366 0\n1174 -234 -215 0 511 368 0\n1175 -235 -222 0 511 369 0\n1176 -238 -243 0 511 374 0\n1177 -239 -202 0 515 377 0\n1178 -240 -209 0 515 380 0\n1179 -241 -216 0 515 383 0\n1180 -242 -223 0 515 385 0\n1181 -243 -230 0 515 386 0\n1182 -249 -273 0 492 427 0\n1183 -250 -280 0 492 429 0\n1184 -251 -287 0 492 430 0\n1185 -256 -267 0 496 431 0\n1186 -257 -274 0 496 435 0\n1187 -258 -281 0 496 438 0\n1188 -259 -288 0 496 440 0\n1189 -264 -275 0 500 441 0\n1190 -265 -282 0 500 444 0\n1191 -266 -289 0 500 446 0\n1192 -267 -248 0 504 447 0\n1193 -271 -276 0 504 449 0\n1194 -272 -283 0 504 452 0\n1195 -273 -290 0 504 455 0\n1196 -274 -249 0 508 457 0\n1197 -275 -256 0 508 458 0\n1198 -279 -284 0 508 461 0\n1199 -280 -291 0 508 466 0\n1200 -281 -250 0 512 468 0\n1201 -282 -257 0 512 470 0\n1202 -283 -264 0 512 471 0\n1203 -284 -271 0 512 472 0\n1204 -287 -292 0 512 477 0\n1205 -288 -251 0 516 481 0\n1206 -289 -258 0 516 484 0\n1207 -290 -265 0 516 486 0\n1208 -291 -272 0 516 488 0\n1209 -292 -279 0 516 489 0\n1210 10 59 0 860 497 0\n1211 -59 -113 0 855 517 0\n1212 -60 -120 0 855 518 0\n1213 -109 -71 0 855 519 0\n1214 -61 -127 0 855 520 0\n1215 -110 -78 0 855 521 0\n1216 -62 -134 0 855 522 0\n1217 -111 -85 0 855 523 0\n1218 -63 -141 0 855 524 0\n1219 -112 -92 0 855 525 0\n1220 -10 296 0 857 845 0\n1221 -44 109 -125 -124 26 -67 62 111 -140 -34 61 63 112 -84 0 403 1194 625 402 1203 414 1193 407 652 621 983 1210 140 1128 152 570 277 1169 289 1158 282 161 1136 166 1148 170 611 255 257 260 142 148 1092 1018 1075 1022 592 35 0\n1222 -85 291 -124 26 -67 62 111 -140 -34 -92 -84 0 420 402 1203 659 652 983 1210 140 1108 1127 151 1114 150 292 1171 277 381 301 1158 416 1184 299 1157 322 272 375 266 274 1219 302 1099 403 547 426 388 1010 984 1111 156 1221 908 907 1038 107 286 1072 348 1103 300 0\n1223 44 28 291 46 94 -67 210 112 95 0 420 983 1210 140 1114 150 277 1158 274 908 907 1038 107 286 1072 348 1103 300 0\n1224 -124 26 -67 -140 -34 36 292 -92 -84 0 983 1210 140 1108 1127 151 1128 152 570 292 1171 277 381 301 1169 289 1158 282 567 299 1177 268 416 1184 390 951 949 161 1148 1157 322 272 375 266 1219 302 402 621 659 1193 1203 487 407 420 1222 22 411 467 388 1010 1111 156 1223 170 611 255 257 260 142 148 1018 1022 1044 107 553 598 984 35 0\n1225 -11 12 110 -75 26 219 61 0 585 1022 0\n1226 -44 60 -75 26 -67 194 61 -84 0 277 1158 284 340 288 983 1210 140 1128 152 570 282 170 611 257 142 1225 35 392 589 1197 41 406 0\n1227 26 -67 -140 -34 36 292 -92 -84 0 983 1210 140 1128 152 570 277 1158 282 161 1148 292 299 1157 322 272 274 1219 1224 505 284 343 340 317 348 288 271 300 1226 1103 418 606 483 393 1225 35 392 589 1197 41 406 0\n1228 44 46 30 -26 -67 210 112 292 -84 0 654 983 1210 140 1114 150 292 1171 277 381 301 1158 322 272 274 302 908 907 1039 1038 107 286 348 300 1103 418 606 1066 483 392 588 393 1197 41 406 0\n1229 -67 -140 -34 36 292 -92 -84 29 0 161 1148 299 1157 1219 292 1151 267 129 127 125 277 983 1169 1210 289 140 1227 154 980 620 1129 262 158 159 172 1228 170 255 257 260 142 148 918 0\n1230 -44 80 129 177 31 -10 194 -92 54 145 96 47 29 0 140 170 255 257 260 142 148 918 0\n1231 19 12 44 94 80 129 37 30 38 31 -10 62 111 -140 -34 61 63 112 292 -231 0 907 908 981 1018 1070 1202 397 69 278 1159 288 360 41 300 393 1103 483 418 0\n1232 -19 70 119 -75 28 -18 21 194 -84 0 292 284 1164 361 301 1171 302 129 127 125 123 148 960 260 86 171 0\n1233 -34 36 292 -92 -84 43 29 91 83 0 292 299 1157 322 272 1177 268 274 1219 1151 267 129 127 125 161 1028 1136 1148 513 416 853 567 1184 851 390 949 951 1229 1047 1210 140 1220 1114 848 150 501 147 847 1135 187 204 247 850 849 159 229 245 156 165 505 158 164 284 618 1164 289 361 301 1230 908 907 1232 981 1231 1070 606 1202 1103 397 300 69 1161 278 333 0\n1234 -227 -296 298 34 0 848 1164 1169 284 277 501 847 997 849 505 0\n1235 31 129 19 227 21 119 -12 44 63 112 292 -84 0 289 292 606 1103 300 1161 333 278 280 69 925 397 419 485 0\n1236 117 19 -10 215 -132 34 -92 43 103 78 29 127 0 1220 848 278 852 1007 1006 1091 1004 501 0\n1237 19 -10 -12 44 -132 34 292 -84 43 103 78 29 127 0 852 1220 1234 140 1114 150 292 1151 267 11 562 1101 299 1157 274 1219 908 606 1103 300 1161 333 1236 74 75 1235 0\n1238 -10 -12 44 -132 34 292 -84 43 103 78 29 127 91 0 292 1151 267 11 562 1101 1219 299 1157 274 606 1103 300 1161 333 278 1178 273 280 45 852 1177 268 137 1139 163 140 1220 908 1114 848 150 1234 361 301 1237 148 636 1141 86 171 251 168 513 416 567 1091 1184 501 390 1059 949 0\n1239 -12 44 -132 34 292 -84 43 103 78 29 127 91 0 292 1151 267 11 562 1101 299 1157 274 903 1219 606 1103 300 360 1238 1102 270 983 904 723 1163 930 872 340 501 284 865 1105 690 0\n1240 -59 -132 -92 91 0 884 903 983 760 904 723 1107 930 872 888 501 774 865 780 889 690 778 505 0\n1241 -42 -18 70 119 12 -10 85 -132 34 36 -92 -84 0 1220 848 997 852 847 849 505 618 140 147 1135 229 158 1114 204 156 159 1033 1032 1234 289 150 409 1198 414 292 299 1157 322 272 1177 268 168 569 1113 1119 1143 211 223 138 143 1232 149 155 22 1018 948 950 411 1054 1187 1004 436 574 393 41 0\n1242 -18 70 119 12 85 -132 34 36 -92 -84 91 0 1240 1210 299 1177 268 1157 274 1219 1241 513 416 567 1061 1184 22 390 0\n1243 291 110 194 28 121 124 -67 12 44 94 23 210 112 -231 0 277 1158 282 322 272 274 1171 302 1223 172 262 154 505 284 1225 343 317 348 271 300 35 1103 392 418 482 0\n1244 26 109 110 219 121 124 12 23 208 0 282 272 505 284 1225 317 35 271 0\n1245 44 -132 34 292 -84 43 103 78 29 127 91 0 292 852 1151 267 11 562 1101 1240 1210 1220 1234 361 301 140 1108 1127 151 1128 152 1114 150 848 409 1198 414 1062 1171 299 375 266 1177 268 1157 322 274 1219 137 1139 163 1239 908 907 1242 1104 277 1091 1009 570 1039 1158 1107 1032 1033 168 569 1113 1143 138 22 411 1187 467 436 388 393 1041 1243 1208 403 99 546 984 1244 154 216 262 158 172 1228 0\n1246 -26 -44 80 -132 -92 54 145 96 47 43 103 78 29 127 91 0 1240 1210 1220 848 140 1128 852 154 849 1129 216 847 159 1104 1091 620 1107 1230 168 1143 0\n1247 -67 12 26 -44 -132 -84 43 103 78 29 127 91 0 611 292 1151 267 11 562 1101 1240 1210 140 1128 152 299 1157 322 272 277 1091 1009 570 1158 1107 505 1244 168 39 1143 1226 0\n1248 -18 26 -44 85 -132 34 36 -92 54 145 96 47 29 91 0 852 1240 1210 1220 1234 289 848 140 299 1177 268 1157 274 1219 147 997 1135 505 159 229 618 1230 1143 168 513 416 567 1061 1184 22 390 0\n1249 43 103 133 83 78 29 127 91 0 1094 125 127 129 292 1151 267 11 137 562 1112 1139 1101 1027 163 1233 1106 852 1062 1240 1210 1220 848 1234 289 1245 170 1246 1248 1104 1091 1247 1107 142 168 257 1143 0\n1250 -43 83 0 169 898 901 1144 900 1145 1210 140 1220 899 902 189 848 805 905 501 207 847 804 161 850 807 1106 1105 852 849 0\n1251 -26 -84 194 -92 96 47 80 292 298 -10 54 29 0 299 1157 1219 421 1220 848 140 1128 154 849 1129 216 262 847 159 158 172 1104 1228 620 1230 0\n1252 -67 26 208 63 -84 194 112 -132 -10 0 272 292 409 1209 140 1128 152 277 1009 570 1158 505 284 343 317 340 348 271 288 300 1226 1103 418 606 483 393 1244 392 589 1197 41 406 0\n1253 -79 19 -92 140 -132 34 -10 0 288 574 1159 1007 0\n1254 34 -10 -103 29 91 83 133 0 140 1114 150 1220 848 389 1183 19 1250 1106 409 852 1209 462 1234 421 480 416 289 417 1107 1003 1002 1101 168 299 1219 565 1143 1157 122 274 292 361 322 301 272 1251 1252 501 147 997 1135 204 505 159 229 156 618 158 1230 908 907 1232 1018 1235 1253 41 393 483 418 1103 300 1161 333 1007 397 641 485 86 419 0\n1255 -10 -103 29 91 83 133 0 389 1200 1250 140 1220 1108 848 1127 1254 161 1028 1136 1148 513 166 173 416 667 1184 1204 473 421 417 1101 299 565 1177 122 292 1233 1171 163 375 1138 241 220 242 266 233 247 155 980 147 1104 1010 1093 1105 402 652 1203 1017 414 0\n1256 -103 29 91 83 133 0 1250 389 1255 1102 983 1047 1107 1028 1106 409 1240 1209 1101 480 417 0\n1257 12 23 26 121 124 219 -78 0 505 284 340 288 287 1155 1215 1244 392 589 1197 987 406 0\n1258 -59 -78 91 83 133 0 1250 270 983 1163 1047 1107 168 1028 1143 1106 173 409 884 1240 723 1002 1209 759 1101 872 421 763 501 147 865 571 1121 690 152 505 284 340 1257 142 1117 162 122 292 974 360 300 0\n1259 -12 -18 -75 194 -84 -141 -10 91 83 0 140 1114 147 204 156 1135 159 618 284 1164 417 1188 395 1218 150 142 974 1117 64 582 1027 907 1235 1232 0\n1260 19 12 30 31 129 80 -10 61 110 0 1018 41 288 574 1159 69 278 0\n1261 -19 94 194 -84 -141 -10 0 417 1188 395 1218 140 1114 150 148 636 188 260 257 170 171 908 907 86 0\n1262 -67 12 -75 -10 -78 0 98 96 140 1128 152 277 570 1158 1257 0\n1263 12 19 -75 -10 -78 0 284 1164 289 1220 848 140 287 1155 272 1215 1262 501 147 618 1135 229 158 159 1260 0\n1264 -75 194 -84 -141 -10 -78 91 83 0 292 1220 848 284 1164 343 361 301 1261 1263 974 1259 300 1104 1161 277 329 0\n1265 -129 -67 75 0 407 620 1193 505 402 0\n1266 -67 292 -12 75 194 -84 -141 -10 0 974 582 64 292 1171 417 1188 395 1218 140 1114 150 277 1169 381 301 1261 1265 1235 159 621 1129 1105 154 0\n1267 -12 75 194 -84 -141 -10 91 83 0 292 1171 302 129 127 125 417 1188 395 1218 140 1114 150 1220 848 142 974 1117 64 582 1027 907 1266 501 147 847 204 850 156 1105 154 654 262 172 259 928 909 171 86 0\n1268 -298 91 83 0 1250 852 509 1028 851 513 853 0\n1269 -26 12 75 194 -84 -141 -10 61 110 298 0 292 1171 1220 848 140 1128 154 849 1129 216 847 159 158 1104 277 1265 1169 381 289 301 1260 1261 0\n1270 194 -84 -141 -10 -78 91 83 0 417 1188 395 1218 33 1220 848 287 1155 272 1215 1268 1264 1267 1269 505 850 847 1104 1252 979 509 0\n1271 -194 -141 -10 91 83 0 1220 848 1143 1148 1026 168 161 513 1106 884 765 758 762 501 997 761 1105 885 0\n1272 34 -18 -75 84 -141 -10 91 83 133 0 1271 173 417 1188 395 1218 1106 409 884 765 1209 885 421 761 758 1107 1002 1031 122 0\n1273 -182 -75 -10 -78 0 140 1114 1117 208 142 148 1263 0\n1274 -34 -96 91 43 0 1028 667 513 0\n1275 -75 -141 -78 91 83 133 0 1258 1210 1271 1270 173 1220 848 1250 1273 162 1027 421 122 1274 1106 1272 706 1002 1104 1065 0\n1276 -124 92 -296 91 83 0 848 850 847 1104 1009 979 509 0\n1277 -141 -78 91 83 133 0 1258 1210 1220 848 287 1167 266 1268 1250 33 1271 173 1270 1275 1276 1105 154 849 544 847 1104 762 1010 1111 219 162 1027 421 122 1274 1106 884 1002 758 0\n1278 -19 -140 28 36 102 -173 -132 129 -67 -92 -157 0 567 299 1177 268 416 1184 390 951 949 409 1198 476 1129 159 414 1009 1033 1032 277 1169 289 1157 1219 71 148 631 1083 1141 188 1090 244 22 164 293 1077 1156 0\n1279 -140 28 36 102 -173 -132 129 -67 -92 -10 61 110 0 140 1128 216 158 1129 159 409 1198 414 1009 1033 1032 277 1169 289 299 1177 268 1157 274 1219 416 567 1184 476 390 949 951 1278 1260 142 602 1140 1078 164 1084 1090 982 22 975 293 412 1190 442 397 1156 1083 1077 0\n1280 -132 -67 75 -92 -10 -78 29 298 91 133 0 277 1169 289 1265 287 1167 266 1155 272 1215 18 409 1009 1209 1105 421 154 544 1142 1010 985 1111 163 156 219 162 1279 1107 1002 1003 168 122 1251 1143 0\n1281 -26 292 194 96 -67 -92 -10 -78 29 298 133 0 421 173 277 1169 289 287 1167 266 18 154 544 1251 1010 122 1111 162 219 0\n1282 -173 31 -34 80 129 -92 -10 61 110 29 91 83 133 0 1250 1028 513 416 1204 421 161 1148 173 1274 140 1108 1127 1128 1114 216 215 158 232 163 1233 122 162 1117 208 142 148 1260 0\n1283 -35 291 4 -124 26 129 -67 -92 -10 53 61 110 0 420 621 277 1169 289 1158 282 570 299 1157 1219 140 1108 1127 151 1128 152 1114 162 658 1117 1137 208 142 172 148 1260 1018 587 1022 35 984 388 555 1182 404 107 286 1044 1166 1223 301 0\n1284 -67 75 -78 29 91 83 133 0 1250 1277 1101 1258 1210 140 1108 1127 287 1167 266 1155 272 1215 1268 1265 1280 509 161 1028 1274 1136 1148 513 166 173 416 1184 1204 421 1281 505 402 541 652 1203 487 414 1283 122 1233 163 220 985 155 1017 0\n1285 75 -78 29 91 83 133 0 1258 1210 1220 848 1268 1284 501 847 850 849 1105 0\n1286 194 96 -18 292 -75 -92 -10 -78 29 133 0 140 1114 147 204 156 1135 229 159 618 421 284 1164 289 1273 162 299 1157 274 1219 150 18 173 1230 122 908 907 1232 1263 1235 0\n1287 -19 62 111 87 136 -132 -140 34 129 -18 80 63 112 -10 110 0 147 1135 159 70 71 1055 1083 1140 164 1053 1059 582 908 1071 65 0\n1288 -119 37 19 62 111 87 136 -132 -140 34 -18 63 112 -10 110 0 582 908 65 982 1071 1057 633 0\n1289 68 119 19 62 111 -132 -140 34 -18 63 112 -10 110 0 1057 1059 982 581 0\n1290 36 119 6 -132 -140 34 -18 -75 55 63 112 -10 -78 0 140 1114 147 204 156 284 1175 296 651 409 1198 414 416 476 420 1050 1051 950 948 1184 390 618 1164 289 150 1215 949 951 1287 1263 1289 142 633 1140 164 1052 1053 86 1060 643 953 0\n1291 -183 -75 -10 -78 0 140 1108 1138 1139 1140 180 142 148 1263 0\n1292 -194 -18 -75 -92 -10 -78 91 83 0 618 1291 163 284 1175 296 1164 289 299 1177 268 1157 274 1219 1215 1143 1148 168 161 513 1106 416 567 409 651 1184 1198 390 414 476 420 1050 948 950 949 951 1290 1287 1288 1263 55 59 61 142 975 0\n1293 -18 -78 29 91 83 133 0 1258 1210 1285 1291 163 284 1175 296 1164 289 1273 1027 1250 1277 1101 299 1177 268 1157 274 1219 1215 618 1292 1286 1274 1106 409 651 1002 1198 416 567 414 476 1184 1290 420 390 908 1050 949 951 170 948 950 1287 257 1263 142 0\n1294 -191 -159 -67 -75 -92 91 83 0 1140 1145 250 195 168 161 513 1106 705 1065 0\n1295 -132 -67 145 35 -75 -92 -10 208 91 133 0 96 299 1157 274 1219 705 1065 1107 1002 1003 168 122 1143 1252 0\n1296 103 29 133 83 43 91 127 0 1249 287 1155 1258 1210 1220 848 1277 1101 1285 1273 162 1027 421 1291 163 1293 1104 1295 509 161 1274 1233 1148 122 173 0\n1297 29 127 91 83 133 0 1250 1256 1296 0\n1298 -34 -92 -53 -67 -75 -176 91 43 0 266 299 1177 308 285 268 1157 274 1219 983 1210 140 1128 152 284 1175 363 293 570 277 367 295 1158 282 296 1132 1134 141 1133 161 1028 650 1136 513 166 416 567 1184 390 1093 949 951 22 411 548 1187 99 403 625 1194 433 1075 392 592 35 0\n1299 -92 -53 -67 -75 -176 91 83 133 0 284 266 1150 343 292 983 1210 140 1108 1127 1175 363 293 296 1250 299 1177 268 308 285 1298 1106 409 651 705 1198 1209 1065 414 421 1107 1002 1003 122 168 569 1045 1113 138 22 163 549 220 99 155 0\n1300 27 46 144 -42 137 39 28 -141 77 87 -67 88 11 0 983 1210 140 1114 168 211 149 1036 1034 107 1016 0\n1301 -132 47 -141 -53 -67 -75 11 91 133 0 417 1205 390 554 762 284 266 1150 343 292 983 1210 140 1108 1127 1175 363 293 286 277 367 295 296 409 884 651 1198 1209 758 414 421 1107 1002 122 168 568 162 656 1113 1137 138 172 1300 155 548 220 22 163 0\n1302 -27 144 39 -140 137 28 -141 77 87 -67 88 11 0 417 1188 416 439 394 395 1218 983 1210 140 1128 102 155 624 1069 1130 221 1016 165 164 301 643 1076 1179 273 615 279 1178 76 300 398 1103 1190 418 474 0\n1303 94 144 39 -140 137 28 -141 77 87 -67 88 11 0 417 1188 416 439 394 395 1218 983 1210 140 1128 152 1114 150 570 277 1158 282 1016 1069 403 625 1194 433 413 475 392 419 35 592 1075 273 615 1178 908 907 300 86 1103 171 645 418 1146 1191 149 445 76 398 0\n1304 -67 102 -75 -176 91 83 133 0 284 1175 296 1132 1134 141 1133 1250 277 983 1010 1158 367 1210 266 282 295 140 570 1150 1128 286 343 152 292 1299 1101 417 1218 1271 554 1188 173 395 1301 509 161 1028 650 1274 1136 513 166 416 1204 439 421 394 122 656 1302 1303 301 643 1179 328 976 285 81 398 99 1190 403 474 1194 433 418 392 35 592 1075 273 615 1178 1103 300 0\n1305 -27 85 -53 104 55 6 169 0 155 548 220 22 163 0\n1306 -53 86 77 94 28 144 87 -141 96 39 -132 -42 129 -18 -222 -29 133 0 417 1205 390 1188 395 568 1218 409 1209 421 1198 414 168 1143 173 1119 143 1113 138 157 1132 1134 147 187 140 1102 270 1163 282 1153 275 571 1211 1133 179 135 1135 159 1121 152 1120 1175 296 1164 289 141 266 1150 363 343 293 292 122 162 1137 238 172 171 1305 1036 948 107 404 1195 434 419 478 392 387 35 1100 271 598 265 530 539 1149 1083 280 86 399 1191 418 1103 300 616 1178 273 315 318 279 285 99 549 592 22 54 534 412 76 1190 398 0\n1307 53 72 121 23 22 102 -176 0 1132 1134 141 1133 136 984 35 271 1212 1154 6 281 0\n1308 -233 27 -53 104 55 137 39 6 219 121 23 235 11 0 266 363 293 282 296 345 365 285 271 99 35 403 549 392 22 1185 411 451 0\n1309 -75 -29 91 83 133 0 157 1132 1134 141 1250 96 284 545 977 1175 296 1304 501 147 618 1120 1121 187 151 152 140 1102 270 1047 571 1163 1107 282 168 1028 1113 1143 1106 138 173 409 1240 651 1002 1198 1209 1101 414 421 417 568 1205 390 1307 266 1150 363 343 293 292 1305 122 1036 162 1137 172 1308 286 294 554 1037 909 1306 950 0\n1310 -173 -141 -451 -42 -176 0 1132 1122 1129 202 229 147 140 1102 983 759 501 763 0\n1311 26 -132 34 75 0 977 505 1009 997 501 0\n1312 -42 75 -176 91 83 0 1132 1250 1028 1106 884 1311 154 1129 1310 229 1101 140 1240 1210 0\n1313 -132 -140 75 -177 0 120 884 1311 760 154 1210 1129 140 229 0\n1314 -173 116 -177 166 0 1129 202 229 147 140 1104 1102 983 0\n1315 -59 -140 83 0 1250 983 1047 0\n1316 -29 91 83 133 0 157 1132 1133 1134 141 1309 1312 513 416 1184 1204 1313 509 161 980 1136 977 505 166 402 850 652 543 1203 487 414 420 1315 1210 140 1220 1128 847 1276 152 1104 299 277 1010 570 1157 1158 388 555 282 1182 426 404 403 1069 286 1072 1044 1166 1098 301 0\n1317 -176 26 -67 -10 91 83 133 0 277 1169 289 1158 282 570 140 1128 152 1316 1297 405 1196 388 1186 393 1214 1116 1122 1132 1304 142 148 1134 1265 505 141 402 621 432 1260 392 587 35 0\n1318 75 -177 26 -140 -67 -10 91 83 133 0 1134 141 1123 148 1317 416 1204 421 277 1169 289 1158 282 570 140 1128 152 1220 1316 1297 405 1186 393 1214 1250 1265 1313 505 509 402 1276 621 161 1274 432 1148 232 392 173 163 35 1233 587 122 1260 162 142 1117 0\n1319 -34 35 84 145 91 43 133 0 161 1274 1148 122 173 0\n1320 -132 -75 -140 -67 43 0 1065 705 706 1101 0\n1321 -141 136 -53 -60 144 137 39 87 88 11 -140 -67 0 266 1150 286 416 277 417 1218 554 1188 1302 1303 395 439 301 643 394 1179 976 328 81 398 285 1190 99 474 592 418 1074 273 615 1178 1103 300 0\n1322 -92 85 -53 -60 137 36 39 87 88 -140 -67 169 0 266 416 1184 390 299 1219 567 1157 1177 274 268 308 1305 951 949 285 99 403 625 592 1194 1075 0\n1323 -60 -141 -34 4 -75 11 -140 -67 22 102 91 43 133 0 650 161 1136 166 277 284 1175 367 295 296 416 1204 421 271 1212 1154 281 6 266 554 1150 286 343 292 1319 656 1321 1302 1303 79 85 301 976 1179 0\n1324 -141 -34 4 -75 11 -140 121 -67 -157 102 91 43 133 0 650 161 1136 166 284 1175 296 416 1204 421 277 1158 282 1108 1127 151 1128 152 417 1188 439 1323 35 392 984 433 434 266 554 403 404 1150 1023 1067 286 343 107 292 656 1319 0\n1325 -109 12 79 -75 -127 0 405 1186 393 1214 392 589 1197 41 406 0\n1326 -177 26 -140 -67 -10 91 83 133 0 1317 416 1204 421 277 1158 282 570 140 1108 1127 151 1128 152 1316 1297 405 1196 388 1250 1134 141 1318 284 540 1175 340 296 367 288 295 1320 509 161 1136 232 166 163 650 1324 1101 1233 1319 162 1117 142 1325 35 271 1212 1154 281 6 266 1322 363 293 0\n1327 11 36 -34 4 -75 109 -140 121 -67 -157 102 91 43 133 0 161 1136 166 277 284 1175 367 295 650 296 1158 282 1108 1127 151 1128 152 35 1324 271 1212 1101 1154 281 6 266 1322 363 293 0\n1328 -75 109 176 26 -140 121 -67 -157 91 83 133 0 416 1204 421 277 1158 1316 1297 405 1196 388 1186 393 1214 1250 284 540 1320 340 509 161 1148 232 163 1327 1225 142 1117 162 1319 292 1229 360 1101 300 974 0\n1329 75 30 26 292 -67 -10 91 83 133 0 1317 421 277 1169 289 140 1114 1220 1316 1297 405 1186 393 1214 1250 1265 505 1009 1276 621 509 161 232 163 1233 1319 162 1117 208 142 148 1260 0\n1330 26 -140 -67 -10 91 83 133 0 416 1204 421 277 1158 570 140 1316 1297 405 1196 388 1250 1317 1326 158 1329 284 540 1320 1328 340 509 37 288 161 1324 1325 232 1101 142 163 1117 1233 162 1319 0\n1331 -92 -140 -67 -10 91 83 133 0 1316 1297 405 1196 388 1330 542 1010 1111 156 154 1142 985 163 1129 159 620 277 1169 289 1186 393 1214 1279 1282 509 0\n1332 -140 -67 -10 91 83 133 0 1316 1297 405 1196 388 1186 393 1214 1268 1250 416 1204 421 1330 96 154 542 1010 1111 219 162 1331 1101 1271 762 758 884 1106 1319 1267 1269 0\n1333 75 -173 -141 -67 -10 91 83 133 0 1250 1332 1107 1028 1106 409 1209 421 1009 1002 168 1143 173 1316 1297 405 1196 388 1186 393 1214 1268 505 542 1010 1111 219 162 122 1267 1269 0\n1334 12 -75 -141 47 -132 121 -67 -157 -127 91 133 0 277 1158 284 340 288 540 96 282 1108 1127 151 1128 152 405 1196 388 1186 393 1214 1225 1325 35 1301 271 1212 1154 6 281 0\n1335 -75 -141 96 -132 194 121 -67 -157 -127 91 133 0 409 1209 421 173 277 1158 284 340 1334 142 1117 162 122 292 974 360 300 0\n1336 -141 -67 -10 91 83 133 0 1250 1332 1107 1028 1106 1009 1002 168 1143 570 140 1316 1297 1335 505 1333 154 0\n1337 35 -75 96 47 -132 -92 -67 91 133 0 409 1209 421 299 1157 983 1210 1295 122 322 292 0\n1338 26 -132 34 -92 140 -67 -127 91 133 0 409 1198 414 299 1177 268 1009 1033 1032 1002 1107 168 1143 173 1113 138 983 1210 140 1108 1127 151 569 1128 152 570 277 1158 282 405 1196 388 1186 393 1214 1311 284 540 1175 340 288 1337 162 1045 1117 142 1225 1325 35 271 1212 1154 281 6 266 363 308 293 285 1305 22 99 549 0\n1339 -67 91 83 133 0 1316 1297 405 1196 388 20 1268 1250 277 983 1169 1210 289 1332 1336 1107 1101 168 1028 1143 1106 173 409 1002 1209 421 1338 154 542 1251 1010 122 1111 162 219 0\n1340 -182 80 129 30 31 -10 -127 0 140 1114 405 1186 393 1214 1117 208 142 148 1260 0\n1341 -140 -19 -132 -92 88 80 129 -18 -10 110 0 140 1108 148 1141 241 163 631 409 1198 414 1220 847 850 1033 120 299 1177 268 1157 274 1219 416 567 1184 476 390 420 951 949 1050 1287 948 0\n1342 -19 94 -84 47 96 -132 -92 88 80 129 -18 -10 110 54 29 91 0 409 1209 421 299 1157 274 1219 140 147 1135 229 159 1114 150 148 636 1141 1341 1107 168 1143 251 1230 171 908 907 86 0\n1343 44 -12 19 -84 292 -92 227 129 31 -10 0 299 1157 274 1219 140 1114 150 908 1235 0\n1344 47 96 -132 -92 35 26 -18 -10 110 61 78 54 29 91 43 133 0 409 1209 421 1198 414 1220 847 850 1033 120 299 1177 268 1157 274 1219 1105 284 1175 296 1164 289 618 140 147 1135 229 158 1108 227 159 187 122 292 361 301 1342 1260 1018 44 142 602 1140 998 164 1343 170 1248 1145 250 24 29 1217 143 189 192 168 951 149 155 513 948 950 1057 953 633 0\n1345 -140 -132 -92 88 227 129 -18 -10 110 61 78 91 43 0 409 1198 414 1220 847 850 1033 120 299 1177 268 1157 274 1219 289 140 147 1135 229 158 1114 204 156 1108 227 159 150 416 567 1341 1184 476 1260 1018 390 420 44 142 602 1050 1051 1140 998 948 950 164 951 949 1288 1289 633 1052 1053 86 1060 643 953 0\n1346 -132 -92 35 26 -18 -10 110 61 78 54 29 91 43 133 0 1220 847 850 1105 284 1175 296 1164 618 1345 1002 1003 1344 0\n1347 -92 -10 91 83 133 0 1316 1297 1339 1220 848 501 147 1135 159 140 229 158 847 850 1268 849 1105 618 284 1164 289 1340 1027 421 162 1108 227 405 1186 393 1214 21 20 1250 1346 509 161 1319 232 1233 163 0\n1348 -84 -141 -18 -10 110 61 91 83 0 1271 1220 847 850 1268 849 1105 284 1164 289 618 140 147 1135 229 158 159 292 1259 361 1260 301 1261 0\n1349 -10 91 83 133 0 1339 1316 1297 405 1186 393 1214 1268 1250 140 1220 848 501 147 847 1135 850 849 159 229 1105 158 284 618 1164 289 1340 162 1027 421 1347 1101 1348 1272 1319 0\n1350 -84 4 -75 23 22 26 121 -141 194 219 102 110 61 0 284 340 282 292 1151 360 307 300 266 974 984 1225 35 271 1212 1154 6 281 0\n1351 -70 101 -141 64 113 0 280 537 1149 1100 265 0\n1352 -21 101 -141 64 113 0 150 539 1110 1100 135 0\n1353 91 83 133 0 1250 1316 1297 405 1214 1186 1196 393 388 1339 1349 1102 270 1211 1047 1153 1163 1107 275 282 168 1028 1113 1119 1143 1106 138 143 173 409 884 1240 723 1002 1198 1209 759 1101 872 414 421 763 417 1218 568 1032 1033 501 1188 1205 147 865 571 395 390 1120 1121 1135 690 151 152 159 1105 284 540 618 1164 1175 340 289 288 1350 122 162 656 1117 1137 238 142 172 171 1225 1325 35 1244 271 1212 1173 1154 294 281 6 266 554 1150 363 286 293 1305 1036 948 950 909 107 404 598 1195 419 478 387 1351 1352 86 399 1191 418 1103 300 616 1178 273 315 318 279 285 99 592 54 412 579 1190 398 442 76 397 1083 0\n1354 -11 144 95 46 77 -93 0 141 596 1115 107 156 0\n1355 -128 129 80 68 31 -59 0 406 575 1189 69 397 0\n1356 -30 129 80 68 31 -59 0 158 576 1123 69 148 0\n1357 -124 -35 110 -93 -34 -59 259 -91 0 162 1137 172 1117 142 298 270 1163 300 348 347 285 1176 379 314 278 286 272 983 709 869 977 501 147 1135 159 1121 152 571 161 1136 166 282 402 619 652 658 1193 1203 407 414 1011 1354 1355 1356 41 288 1168 271 35 392 599 434 107 404 0\n1358 -35 110 -93 -34 -59 259 -91 0 298 1176 300 379 272 983 709 869 977 501 147 1121 152 571 270 1163 162 1117 142 1357 1105 1244 284 392 589 340 1197 288 406 41 0\n1359 -84 224 -93 23 121 26 72 -34 259 -91 0 298 347 285 286 300 161 1136 166 292 1171 343 302 378 284 271 505 402 652 659 1203 414 1011 1354 35 392 599 434 107 404 0\n1360 -93 -34 -59 259 -91 133 0 983 709 869 977 501 147 1121 152 571 161 1148 173 666 270 1163 282 298 1176 303 300 348 1359 122 610 1358 0\n1361 -75 19 118 20 69 -18 -34 0 161 1136 147 247 165 1135 159 284 618 1164 289 955 981 76 0\n1362 -103 36 -34 104 6 55 0 389 560 1200 22 411 0\n1363 276 119 21 -280 94 64 113 45 -274 -141 0 456 465 387 419 1351 86 0\n1364 -101 77 144 46 95 4 -18 102 -141 0 147 1120 151 417 387 527 1192 400 454 6 404 554 107 0\n1365 101 119 21 35 95 94 -18 -75 64 113 45 52 -19 -141 47 145 96 0 147 1351 1100 86 135 960 1110 156 204 0\n1366 -59 -19 124 -127 -141 -34 -91 0 161 1148 148 260 171 1123 158 529 405 1196 388 1186 393 1214 417 1188 395 1218 173 666 877 298 1176 303 270 1211 983 709 743 575 1153 1163 869 970 275 977 1105 991 501 284 540 142 147 571 967 384 1117 257 1120 1121 302 162 170 151 152 1350 122 410 607 657 1199 1103 420 418 583 1191 399 1365 387 527 1364 1192 286 400 1150 6 266 0\n1367 -132 -12 62 111 -26 20 27 13 -11 -67 124 265 0 141 154 1142 245 164 166 983 1210 1220 398 409 852 1032 602 1198 442 54 414 397 577 590 99 936 295 631 1174 1006 278 0\n1368 -83 -19 62 111 37 20 13 -67 0 148 1141 165 983 1210 277 1169 291 630 356 953 295 0\n1369 216 39 137 87 88 20 -67 118 0 279 976 935 0\n1370 -27 39 137 88 175 91 144 77 126 0 156 102 155 1069 223 1107 168 0\n1371 -42 27 186 137 88 28 144 77 126 0 166 168 1036 252 107 172 0\n1372 -83 175 91 144 77 -67 124 273 0 156 983 1210 866 404 291 694 1170 692 296 505 154 648 1142 166 1370 1371 513 416 1069 453 403 0\n1373 -26 -133 194 28 77 126 0 154 927 262 172 0\n1374 -137 -75 83 0 414 650 1198 1106 409 0\n1375 -132 175 -75 91 144 77 -67 124 126 43 0 866 983 1210 692 694 1353 657 156 107 1374 284 1175 296 1320 1033 1107 1370 1036 0\n1376 175 -75 91 144 77 -67 124 273 43 0 866 983 1210 692 694 1374 284 1175 296 404 156 1375 509 161 1028 1136 513 166 416 1069 453 403 0\n1377 -34 28 137 88 91 144 77 273 43 0 404 161 1028 1136 513 166 416 1069 453 403 0\n1378 -75 91 144 77 -67 124 273 102 -141 0 983 1210 140 1108 1127 866 404 417 1205 390 32 284 692 1175 694 296 1353 1374 657 1376 1111 1010 266 554 363 107 293 1377 1106 1320 1033 1107 168 568 1036 1113 1305 138 0\n1379 91 144 77 -67 124 273 -127 -141 0 983 1210 404 405 1196 388 1378 505 542 1010 1111 156 1372 1271 1353 1373 0\n1380 -132 84 133 35 -91 0 298 1176 303 133 409 1003 1209 122 421 0\n1381 84 133 83 35 -91 0 298 1176 303 1380 509 161 666 1148 122 173 0\n1382 -75 83 -91 -67 0 983 1210 868 866 692 701 695 703 693 702 1106 0\n1383 273 77 124 -83 91 -67 -127 -141 0 983 1210 866 694 692 505 154 1129 159 277 1169 289 1265 140 1128 216 158 1340 162 405 1196 388 542 1010 1111 156 291 1181 303 1001 1000 404 1379 112 654 927 122 0\n1384 -144 77 35 28 -26 96 145 47 0 112 117 654 927 122 0\n1385 126 94 144 143 77 175 186 137 -230 91 -67 -141 0 156 166 277 1169 356 295 1170 296 983 1210 140 1114 150 417 1188 395 1218 1370 1371 513 416 1069 1303 439 403 625 141 394 1194 245 164 1075 273 615 1178 908 907 300 86 1103 171 645 418 1146 1191 149 445 936 398 0\n1386 44 -126 94 -67 -141 0 983 1210 140 1114 150 417 1188 395 1218 908 907 1038 0\n1387 94 143 77 -26 -83 91 -67 -127 -141 0 1000 1001 291 1181 303 405 1196 388 542 1010 1111 156 983 1210 154 1129 159 277 1169 289 866 694 692 1265 140 1128 216 158 1340 162 1384 1142 166 648 356 295 1170 296 1186 393 1214 417 1188 1385 1016 141 245 164 1386 170 1145 250 143 189 168 149 513 416 615 439 394 1368 1260 952 1369 601 1160 54 294 0\n1388 -94 -26 -83 91 -67 -127 -141 0 983 1210 154 1129 159 277 1169 289 866 694 692 1265 140 1128 216 158 1340 162 1142 166 648 291 356 295 1181 303 1170 296 1001 1000 405 1186 393 1214 417 1188 395 1218 301 382 361 278 292 122 637 1260 69 142 397 635 1140 1189 1202 164 972 413 170 250 168 513 416 615 1074 439 394 0\n1389 77 124 -83 91 -67 -127 -141 0 866 983 1210 694 692 505 1388 1383 1387 1195 419 0\n1390 37 62 111 160 -26 -83 -67 -127 0 983 1210 140 189 149 143 1128 154 216 158 1142 166 1129 159 648 866 694 692 1265 277 1169 291 356 295 1170 296 289 405 1186 393 1214 952 1368 1369 1260 1160 601 294 54 0\n1391 159 -173 129 -67 -127 0 983 1210 140 1128 216 158 1129 159 277 1169 289 405 1186 393 1214 142 188 1260 148 0\n1392 -44 -26 -83 91 -67 -127 259 0 866 983 1210 694 692 1265 154 1391 1140 164 170 1145 250 168 513 416 615 439 1390 394 0\n1393 124 -83 91 -67 -127 -141 0 866 983 1210 694 692 140 1108 1127 151 1128 152 570 277 1158 282 405 1196 388 417 1188 395 1218 505 542 1389 286 552 348 984 300 1392 1103 595 35 271 1212 1154 6 281 0\n1394 -141 -77 112 44 109 102 -67 0 277 1158 286 348 300 1150 266 983 1210 140 1108 1127 151 1128 152 570 282 1218 552 1103 595 35 271 1212 1154 6 281 0\n1395 -77 112 44 109 102 -67 0 983 1210 805 899 898 277 1158 286 348 300 1394 1101 299 1157 274 1066 1103 0\n1396 -132 27 125 76 -26 0 154 1142 166 97 409 1032 1198 99 414 0\n1397 -144 284 39 27 91 88 0 414 420 1037 476 513 416 0\n1398 30 29 -36 61 54 80 -10 31 129 251 34 0 140 1108 163 1139 180 148 1018 1138 1140 142 1260 52 1215 991 1012 0\n1399 -36 11 61 54 -124 251 39 137 27 -83 0 97 977 119 997 501 983 1210 140 1108 1127 151 1128 152 570 277 1169 289 1158 282 621 402 1193 407 291 1170 296 1017 1019 1398 587 35 392 1185 448 405 1012 287 541 1167 984 266 0\n1400 -287 -76 281 62 -109 111 -67 284 -445 0 594 392 469 412 277 1158 285 345 294 54 143 1119 168 983 1210 805 899 898 476 473 417 1101 756 1095 754 1107 0\n1401 -102 36 251 104 6 55 -109 111 -124 -83 0 951 402 1203 392 469 412 97 977 119 997 501 983 1210 805 899 898 792 993 894 277 1158 414 653 291 1170 296 883 388 426 467 403 411 22 550 99 285 594 345 294 54 143 1119 1145 168 170 1400 416 1107 298 893 612 371 787 300 1101 417 1218 1188 1103 395 0\n1402 -76 140 62 135 -109 111 43 482 -10 219 0 285 594 345 294 54 143 1119 1145 168 170 1107 298 893 612 371 787 300 1101 417 1218 1188 1103 395 0\n1403 -125 102 36 104 6 55 -109 22 235 0 392 1185 403 451 411 22 293 547 363 984 266 0\n1404 140 125 62 135 -109 111 482 -67 137 39 235 0 983 1210 805 899 898 140 1128 277 367 1158 296 1402 99 155 593 1147 221 172 164 54 143 1119 1145 168 170 1107 298 893 1011 612 373 372 787 302 301 1101 417 1218 1386 1188 395 1103 300 599 348 107 286 0\n1405 -177 -173 -487 0 1129 1123 229 1314 140 897 930 1102 904 796 797 903 1101 0\n1406 -505 508 -26 0 900 1210 1220 899 848 805 1104 806 804 0\n1407 -84 210 30 79 110 -142 128 0 292 606 322 41 272 0\n1408 -35 30 79 110 -142 128 0 162 608 1117 41 142 0\n1409 -26 -142 -140 -83 -109 0 416 1204 418 483 393 392 1197 464 410 133 1001 669 895 291 1181 303 406 154 808 588 1405 158 1132 157 1406 898 1020 1408 122 606 1407 991 987 1157 299 1101 417 562 480 11 389 0\n1410 -67 -75 -10 -83 0 866 694 692 0\n1411 -91 85 36 134 -141 0 417 1205 390 298 566 1152 22 268 0\n1412 -83 -103 -141 225 0 417 389 1200 473 416 411 1205 390 291 561 354 293 1411 513 168 568 1113 22 138 0\n1413 -141 225 78 127 -84 133 176 0 292 1151 267 157 417 562 1205 11 389 1200 428 411 409 1412 1353 509 161 560 232 1411 163 0\n1414 -43 26 0 977 898 1250 900 119 1210 899 805 1104 997 804 505 807 0\n1415 -288 281 134 85 36 91 55 0 1205 473 390 416 22 1107 138 168 1113 0\n1416 -6 91 -92 0 138 567 1113 1107 168 0\n1417 -104 91 -92 0 390 569 1184 513 416 0\n1418 -109 102 144 46 53 95 28 -141 22 0 417 1188 392 984 434 552 404 107 0\n1419 62 142 37 38 136 143 87 94 -141 -140 0 895 797 1210 140 1114 150 416 417 1188 439 394 395 1218 1071 1052 1053 582 86 0\n1420 142 37 38 136 143 87 94 -141 -140 0 417 1188 395 1218 1419 273 615 1178 1103 300 0\n1421 -19 35 -75 47 -83 -141 -140 -18 0 291 284 1164 356 295 1181 384 302 416 1204 421 147 895 797 1210 140 1114 204 156 963 303 150 417 1188 395 1218 148 960 630 1141 165 244 164 1420 65 418 581 908 1191 86 445 171 645 398 1146 76 149 0\n1422 -45 136 38 118 87 -140 0 171 645 1146 76 149 0\n1423 -133 126 77 95 28 -75 0 410 657 1199 107 420 0\n1424 -143 44 35 -83 -140 95 28 -75 -141 43 -18 0 1218 895 797 1210 417 1188 395 908 284 1164 289 618 147 1135 159 133 1000 1421 1018 291 1181 303 119 140 1108 227 157 229 158 1114 150 416 1204 480 389 421 96 68 419 626 1195 485 404 397 1004 278 1159 288 1423 1020 122 1235 562 1263 991 11 0\n1425 -68 -45 44 19 35 47 -83 29 30 -10 292 129 -75 -141 43 31 0 1218 417 1188 395 908 284 1164 289 1018 291 1181 303 140 1114 150 480 389 421 278 639 1159 1020 122 288 1235 562 1263 991 11 0\n1426 -142 35 -83 -140 95 28 -75 -141 43 -18 0 133 1000 1421 284 1164 291 356 295 416 1204 421 1181 963 147 1135 895 797 1210 140 1108 227 157 229 158 1114 150 289 618 417 1188 395 1218 159 65 418 581 908 1191 445 398 1424 86 171 645 1146 1425 149 69 921 0\n1427 12 5 79 54 128 19 29 30 103 -10 -75 0 1263 991 11 0\n1428 -143 83 28 -140 -18 -75 0 133 1353 410 1199 420 1374 416 284 1175 296 96 1414 98 419 626 1195 404 453 1377 403 1106 1069 1033 0\n1429 -132 -141 -140 -18 -75 0 895 797 1210 884 765 758 885 761 0\n1430 94 87 136 -141 38 37 143 -10 -140 0 417 1188 395 1218 140 1114 150 416 1420 65 418 581 908 1191 86 445 1422 398 0\n1431 -141 -34 83 -140 -18 -75 0 147 1135 161 234 165 96 1414 67 1047 1210 140 229 233 164 1136 166 1114 204 156 1428 133 1353 410 1199 420 1374 416 284 1175 296 417 1218 1188 395 439 1050 394 948 950 1430 301 637 643 1179 279 1361 398 1190 474 418 982 953 273 615 1178 1103 300 0\n1432 -94 87 136 111 62 63 112 38 37 143 -10 -140 0 1053 92 643 1060 953 0\n1433 -34 83 -140 -18 -75 0 147 96 1414 67 1047 1210 140 1114 204 156 1428 150 1135 1108 227 229 133 1353 410 1199 420 1374 416 1184 390 284 1175 296 161 1136 233 232 234 166 164 163 165 1431 1101 299 1219 1416 1157 1177 274 268 1050 951 949 948 950 1053 1052 1432 86 582 908 1071 65 0\n1434 111 62 37 38 94 87 136 63 112 143 -10 -140 0 140 1114 150 1053 1052 86 582 908 1071 65 0\n1435 -36 5 -132 34 103 -10 251 -18 -75 0 147 1135 140 1108 227 157 229 158 159 618 284 1164 289 163 559 1398 1291 1214 11 0\n1436 -37 54 111 55 5 6 -132 103 -10 104 -18 -75 0 147 1135 140 1108 227 157 229 158 159 618 284 1164 289 55 59 61 603 975 142 188 148 1018 1260 1427 52 0\n1437 -38 83 -140 -18 -75 0 416 1184 390 96 1414 67 1047 1210 133 1353 410 1183 389 1433 1106 1429 1101 1416 563 299 1177 268 1435 949 1157 274 1219 1061 22 293 1172 267 1436 951 98 1033 284 1175 296 1374 1199 420 1050 950 948 147 1135 140 1108 227 157 229 158 159 618 1164 289 633 1083 71 574 1018 1427 45 1289 1288 0\n1438 111 136 -140 87 62 63 112 38 37 143 -10 0 1432 1434 0\n1439 83 -140 -18 -75 0 416 1184 390 133 147 67 284 1175 296 96 1414 98 1353 1047 1374 410 1210 1183 1199 140 389 420 1114 204 156 1428 1433 1106 1033 1429 1101 299 1219 1416 563 1157 1177 274 268 1050 1061 948 950 1435 951 949 22 293 1172 267 1436 1437 1438 0\n1440 -62 63 112 136 38 87 143 -10 -140 0 140 1114 150 416 273 615 1178 908 907 300 1103 418 1191 445 398 1422 86 301 643 1179 76 279 0\n1441 -18 -75 -94 168 -140 0 416 1204 421 133 147 1439 204 291 1000 156 1181 963 0\n1442 -75 -94 -37 -10 -140 0 301 1179 1220 848 140 164 1140 188 905 902 901 1128 221 155 1108 1127 151 152 1114 416 1184 390 133 284 1175 296 1441 501 277 1410 570 1320 1158 328 1374 509 282 285 161 1136 166 245 99 141 403 592 426 453 35 388 392 1185 454 417 1101 299 1416 1177 268 1403 163 549 985 0\n1443 -36 -125 102 186 -67 0 163 549 985 0\n1444 -34 -37 76 -67 83 75 -140 0 1315 1210 140 1128 164 221 155 277 1158 282 570 1108 1127 151 152 133 1353 410 1183 389 1220 416 1184 390 161 1136 233 166 245 980 141 505 402 652 1276 1203 425 299 1416 563 414 388 1177 99 1019 268 403 592 35 392 1185 451 448 411 405 1443 22 293 547 1172 984 267 266 11 1167 287 0\n1445 -37 76 -67 19 83 75 -140 0 277 1169 289 1265 133 1353 410 1183 389 1315 1210 1250 164 1140 142 1444 1106 1311 603 1313 154 158 1132 1129 1391 157 159 1091 1260 1215 0\n1446 -37 83 75 76 -67 -140 0 983 1210 140 164 1445 1140 148 188 0\n1447 63 112 136 38 87 143 111 37 -10 -140 0 1440 1438 0\n1448 -63 43 0 274 1218 1157 1101 299 0\n1449 -31 75 -67 0 159 621 1129 1105 154 0\n1450 -78 250 110 75 -67 159 -10 0 1449 1265 277 1169 289 1158 282 570 140 188 148 142 1108 1127 151 1128 152 287 1155 1167 272 266 1260 158 1134 216 141 154 505 402 541 587 425 35 388 984 0\n1451 -127 110 75 -67 159 -10 0 277 1169 289 1265 140 188 148 1449 1018 1158 282 570 142 1128 152 405 1214 1391 1186 1260 154 505 1022 402 587 432 35 392 0\n1452 -133 103 54 110 75 -67 -92 159 -10 0 1451 140 1108 1127 410 563 1183 1450 11 157 215 154 505 402 1019 425 388 0\n1453 78 29 60 -125 26 133 103 127 128 54 110 -83 219 121 55 210 6 43 12 -157 251 0 403 426 388 291 1170 119 282 1108 1127 151 1128 152 390 1025 1012 322 1403 272 35 1022 0\n1454 26 133 103 127 128 54 -83 75 76 121 -67 55 210 6 43 -37 -157 251 0 291 1170 296 605 277 1158 282 1128 164 221 155 1140 142 1108 1127 151 152 505 402 653 1203 414 99 403 592 426 388 1019 1453 287 541 1155 1167 272 266 1022 984 35 0\n1455 103 75 76 -67 -92 -37 -10 -140 0 164 1140 1446 605 1451 277 1169 289 1265 140 188 148 1449 1018 299 1177 291 310 267 570 268 1157 133 1416 1220 848 905 902 901 142 1108 1127 416 1184 895 1452 1454 154 1405 215 158 157 1260 49 272 987 322 1025 0\n1456 75 76 -67 -92 -37 111 -10 -140 0 277 1169 289 1158 282 570 299 1177 268 1157 133 1416 140 164 1140 188 148 1128 221 155 142 1108 1127 151 152 416 1204 421 1184 390 1265 1446 291 1000 605 1170 1181 296 303 1449 1455 389 565 561 1183 410 122 292 322 272 1260 158 1134 216 141 154 505 402 653 587 1203 35 414 1401 99 1403 0\n1457 76 -67 -92 -37 111 -10 -140 0 277 1158 282 570 299 1177 268 133 1416 1220 848 140 164 1140 188 905 902 901 1128 221 155 1108 1127 151 152 416 1184 390 1456 284 1410 1320 1175 1374 509 296 161 1136 166 245 99 141 403 592 426 35 388 1443 1403 0\n1458 102 85 71 120 53 186 -76 55 104 6 -67 22 0 985 6 163 546 22 0\n1459 -140 -92 -37 -75 -67 -10 0 299 1177 268 1157 1410 1382 1417 1416 164 60 1353 410 1199 420 284 1175 296 1374 805 899 898 277 1158 282 570 140 1108 1127 151 1128 152 1320 1457 509 285 594 161 308 1136 266 245 141 35 271 1212 1154 319 281 344 286 293 1458 388 555 1182 1377 0\n1460 34 -54 274 83 85 104 6 202 0 268 1106 989 409 22 459 411 0\n1461 274 78 103 5 83 85 104 176 6 202 0 157 268 405 11 1460 161 558 232 22 163 0\n1462 34 135 -158 91 -223 53 -92 102 83 75 85 202 104 6 -67 0 277 1158 345 294 1165 295 299 1157 1219 1265 268 1106 1311 154 1142 245 985 164 163 951 949 22 54 1090 143 1107 1119 168 0\n1463 -186 83 75 0 1136 1142 161 154 1106 1311 0\n1464 -92 44 42 482 284 109 -76 28 102 -67 0 277 285 1180 381 301 106 105 104 103 101 983 1210 805 899 898 1448 140 1114 150 1219 787 908 907 1395 893 1038 1397 513 1069 0\n1465 -13 -34 -124 109 -76 28 102 -67 0 983 1210 805 899 898 1028 791 894 402 1203 277 1158 285 345 1448 143 1145 170 1464 979 1101 298 612 417 371 1188 300 395 1103 0\n1466 -135 202 109 -134 -76 102 -67 0 106 105 104 103 983 1210 140 1108 1127 151 1128 152 570 277 1158 282 1086 590 35 0\n1467 -60 186 85 55 -76 53 102 104 6 -67 0 983 1210 140 1108 1127 151 271 1212 1154 1458 281 0\n1468 -141 -26 194 93 -13 109 94 28 102 83 -67 0 143 1145 170 983 1210 805 899 898 1448 417 1386 1188 395 1395 1103 1373 612 1353 0\n1469 -34 93 -13 109 75 -76 28 102 83 -67 0 143 1145 170 277 285 1180 381 301 983 1210 805 899 898 1448 140 1114 150 161 1465 1148 1105 1468 1101 1219 908 907 1395 1103 1038 1373 612 1353 0\n1470 -92 34 93 202 -13 135 -158 75 85 -223 53 102 83 104 6 -67 0 143 1145 170 983 1210 805 899 898 1448 1219 1462 1103 612 0\n1471 -238 -13 135 -158 109 75 85 -76 53 102 83 104 6 -67 0 143 1145 170 277 285 1180 381 301 1158 345 1010 1111 156 983 1210 805 899 898 1448 1152 371 300 1469 1106 1311 1470 1101 417 1468 1188 1271 395 612 1103 0\n1472 75 85 55 -76 53 102 83 104 6 -67 0 277 285 1180 381 301 1158 345 294 106 105 104 103 1010 1111 156 983 1210 140 1108 1127 151 805 899 898 1128 152 570 282 1463 985 163 951 949 22 546 984 1467 35 141 590 245 164 54 143 1119 1145 168 170 1471 298 1353 513 410 613 1199 1469 420 1106 884 758 762 1101 1097 1098 0\n1473 -94 118 39 -140 87 88 137 -67 0 301 643 1179 1369 0\n1474 -125 55 37 6 112 102 -140 186 87 88 137 -67 0 416 1184 390 166 983 1210 805 899 898 1448 403 625 1443 1194 951 949 1075 0\n1475 111 12 -44 142 28 125 210 37 112 109 118 -140 39 -133 137 -75 -67 0 277 284 1175 367 295 296 983 1210 140 170 1145 189 149 1369 1160 294 615 609 64 805 899 898 1448 982 1067 96 1128 152 570 1158 282 54 412 577 1201 935 393 99 1225 1079 1044 1423 0\n1476 -36 202 -34 251 186 -75 -67 0 163 1093 242 0\n1477 -54 -34 36 104 55 6 0 267 558 1172 22 293 0\n1478 28 94 95 -141 194 -140 210 39 -133 137 -75 -67 0 410 417 1188 437 393 395 1199 420 277 284 1175 367 295 657 296 96 983 1210 140 1128 152 570 1158 282 1223 170 609 257 142 1225 1044 1303 0\n1479 -28 -141 102 -67 0 156 554 1111 1010 0\n1480 -94 112 -140 62 111 39 137 -75 -67 0 277 284 1175 367 295 296 983 1210 805 899 898 1448 1473 81 85 1074 1442 0\n1481 210 95 28 94 -140 39 -75 -67 0 983 1210 1410 805 899 898 1320 509 161 1148 1136 416 1184 390 1382 1353 410 1199 277 284 1175 367 295 657 1158 340 288 296 1374 1448 140 1478 1101 299 1219 1416 1459 1177 1223 268 1476 65 170 609 615 949 982 1145 1294 952 189 142 149 1369 1160 294 54 412 577 1201 936 393 1475 392 589 1197 41 406 0\n1482 -44 -141 28 94 -140 39 -75 -67 0 983 1210 1410 1382 1353 410 417 1188 437 393 1199 479 388 805 899 898 1320 509 161 1148 420 277 284 1175 367 295 296 1374 96 140 1108 1127 151 1128 152 570 1158 282 170 609 257 142 1225 1303 286 552 600 1150 35 266 271 1212 1154 6 281 0\n1483 -77 44 -141 95 28 -75 -67 0 983 1210 1410 1382 1353 410 1199 417 479 388 1188 395 420 657 140 1108 1127 151 286 1395 1150 1418 266 0\n1484 95 28 94 -140 39 -75 -67 0 983 1210 1410 1382 1353 805 899 898 1481 1157 299 1101 1482 1386 1483 1423 0\n1485 -141 28 94 -140 39 -75 -67 0 983 1210 1410 1374 284 1175 296 1484 1067 403 1194 413 805 899 898 1320 509 1382 1353 410 1199 420 113 1377 1195 419 625 161 1136 277 367 295 1303 1430 141 164 245 0\n1486 28 94 -140 39 -75 -67 0 983 1210 1410 805 899 898 1320 509 161 1136 1382 1353 410 1199 420 277 284 1175 367 295 296 1374 1484 113 1067 1377 1182 388 1485 1101 299 1219 1416 1459 1177 1474 268 0\n1487 112 -28 94 -67 0 983 1210 140 1128 156 224 170 805 899 898 1448 1114 150 908 907 1039 0\n1488 -112 43 0 395 1219 1188 1101 417 0\n1489 77 44 -132 -75 -141 94 -67 0 983 1210 805 899 898 1448 1488 907 908 1386 417 1410 1382 1353 410 1199 479 388 420 98 140 1114 150 1378 1375 1195 1131 419 171 86 0\n1490 44 -132 -75 -141 94 -67 0 983 1210 805 899 898 1488 1487 1489 113 1483 0\n1491 39 -75 -141 94 -67 0 417 983 1210 1410 1382 1353 410 1199 479 388 1188 437 393 420 277 284 1175 367 295 657 296 1271 1374 96 805 899 898 1488 1487 140 1108 1127 151 1128 152 570 1158 282 1486 1107 168 1028 1106 1490 170 609 224 257 223 142 155 1225 1300 286 552 600 1150 35 266 271 1212 1154 6 281 0\n1492 -75 -141 94 -67 0 983 1210 1410 1491 166 651 1136 509 161 0\n1493 61 110 26 109 19 12 75 -67 0 505 983 1210 277 1169 289 1265 1449 1018 140 1128 152 570 1158 282 1260 1022 587 35 0\n1494 110 133 26 103 54 176 109 -91 19 159 83 75 -141 -67 0 157 983 1210 277 1169 289 1265 1449 1018 142 1451 1493 47 49 272 987 1155 11 1413 137 1381 1112 162 0\n1495 -85 218 125 39 -102 88 137 0 293 550 344 99 285 0\n1496 -91 87 88 39 37 36 -141 137 135 -44 -67 0 417 1205 390 983 1210 140 170 1145 189 149 143 298 566 617 1152 268 951 54 952 294 1369 1160 0\n1497 -110 62 111 39 -83 137 160 -67 0 277 1169 291 356 295 983 1210 140 189 149 143 605 1021 952 624 935 953 80 0\n1498 37 12 36 -83 -92 -124 -44 -67 0 170 1145 402 1203 414 653 983 1210 791 894 787 893 1417 1416 299 1177 268 949 951 1497 277 1169 291 356 295 1181 303 1170 296 1001 1000 1157 98 97 140 189 149 1128 224 156 143 152 570 1158 282 952 1368 1369 1160 294 54 412 577 469 936 935 392 99 1397 1493 285 590 272 609 1180 1044 35 322 302 598 292 107 122 172 162 1137 0\n1499 -61 12 36 -83 -92 -124 -44 -67 0 983 1210 277 1169 289 98 1265 621 140 791 894 787 893 1416 1417 299 1177 268 949 1498 59 170 1145 143 61 975 188 148 1018 402 1203 414 653 951 1497 1451 291 1181 303 1001 1000 1157 805 899 898 47 49 272 609 987 1155 322 354 292 293 122 22 565 411 1025 467 1019 388 0\n1500 12 36 -83 -92 -124 -44 -67 0 170 1145 402 1203 414 653 983 1210 791 894 787 893 1417 1416 299 1177 268 949 951 1497 291 1181 303 1170 296 1001 1000 1157 98 1265 621 97 140 1128 224 156 143 1108 1127 151 152 570 277 1169 289 1158 282 1498 59 61 164 975 221 188 155 148 1397 1018 1499 1022 1493 1044 594 99 1457 403 1403 513 1208 7 9 388 1036 1283 1182 404 450 107 410 659 122 0\n1501 -86 87 88 39 137 20 -67 0 983 1210 294 578 1160 1369 0\n1502 -109 -141 36 135 111 104 55 6 -83 -124 -67 0 983 1210 800 896 795 895 417 1205 951 291 1170 653 402 1203 414 791 894 140 1108 1127 151 1401 1404 1403 0\n1503 19 12 -141 110 36 104 55 6 109 -83 -124 -67 0 983 1210 800 896 795 895 277 1169 291 356 295 1170 296 1181 653 402 1203 414 1193 98 1265 621 97 805 899 898 1488 1448 140 1114 150 289 1018 1493 47 49 272 1214 987 1155 379 354 1412 300 293 22 411 556 467 388 1019 11 267 1020 1151 410 609 358 465 908 907 1103 298 419 418 513 1191 168 443 1113 211 397 1041 149 69 1034 639 86 0\n1504 -208 -159 140 104 55 6 135 111 243 43 0 1488 1448 1173 379 294 300 975 143 1119 1145 168 170 1107 1103 612 0\n1505 -91 44 -19 -141 62 111 39 -83 137 -67 0 983 1210 805 899 898 1448 1488 907 908 140 148 1141 244 164 277 1169 291 356 295 1170 296 1114 150 298 372 301 957 1368 612 1103 300 1161 336 1369 398 647 1207 86 419 0\n1506 -189 -19 62 111 -83 -67 0 983 1210 140 148 1141 244 164 1114 1119 211 143 149 1368 0\n1507 -19 140 -141 62 36 135 111 39 -83 137 -67 0 277 1169 291 356 295 1170 296 983 1210 140 148 1141 244 164 1506 168 1107 1496 1505 0\n1508 -91 -12 -141 36 104 55 6 111 -83 -124 -67 0 142 1140 164 402 1203 414 653 983 1210 800 896 795 895 951 601 1507 44 277 1169 291 356 295 1170 296 119 98 1265 621 805 899 898 1488 1448 289 298 1496 372 358 301 957 1501 975 612 1103 300 1161 336 333 1369 278 81 69 1015 397 0\n1509 -12 -141 36 104 55 6 111 -83 -124 -67 0 983 1210 800 896 795 895 277 1169 291 356 295 1170 296 653 402 1203 414 140 1114 142 601 1508 513 168 1119 211 143 149 975 1501 0\n1510 -141 110 36 109 104 55 6 111 -83 -124 -67 0 951 277 1169 291 356 653 402 1203 414 983 1210 800 896 795 895 1509 1503 1506 1507 168 57 61 1107 1368 298 957 372 301 0\n1511 125 94 291 -140 44 -92 88 39 137 -67 0 983 1210 805 899 898 1488 1487 420 1097 1098 0\n1512 94 291 -140 44 -92 62 111 87 88 39 137 -67 0 983 1210 805 899 898 1448 1488 907 908 1511 105 403 625 1457 1194 1070 0\n1513 -140 44 -92 62 111 87 88 39 284 -67 0 414 983 1210 805 899 898 1488 1448 277 416 476 1512 93 301 1473 1179 81 85 328 1447 285 1457 0\n1514 -94 -42 87 88 39 137 -67 0 983 1210 140 1114 168 211 149 301 646 1179 1369 0\n1515 -37 291 110 -42 44 111 -92 -83 -124 -67 0 983 1210 805 899 898 1488 402 1203 414 653 291 1170 296 277 1169 356 295 1514 1487 140 1114 168 211 149 1501 1119 143 883 756 754 1001 1000 1417 1416 1181 299 376 267 1177 268 1157 303 98 1128 61 164 975 221 155 1036 1223 172 659 1137 162 122 410 1452 1183 389 0\n1516 -135 118 12 -92 36 -83 -124 -67 0 983 1210 140 1114 883 756 754 402 1203 653 291 1170 296 277 1169 356 295 1417 1416 299 1177 268 949 951 1500 1513 513 168 211 149 414 1119 1497 1506 98 97 412 577 469 936 935 392 99 1493 272 1155 354 293 22 411 1466 467 388 0\n1517 135 44 12 62 111 -92 -83 -124 -67 0 277 1169 291 356 295 402 1203 414 653 1170 296 983 1210 140 1114 883 756 754 1513 513 168 211 149 1501 289 98 1265 621 1506 1018 1119 1497 143 1001 1000 299 1157 1181 303 791 894 97 805 899 898 1488 1448 54 1515 1199 1208 410 403 1404 1493 47 49 272 379 322 300 292 1103 122 1408 0\n1518 12 -92 36 -83 -124 -67 0 883 983 1210 756 754 1416 1417 299 1177 268 951 949 277 1169 291 356 295 1170 296 653 402 1203 1500 1513 513 168 1119 143 1517 61 1516 952 0\n1519 -167 62 111 91 -92 87 88 39 284 -67 0 983 1210 140 1114 1146 211 255 168 170 1107 1513 0\n1520 -92 36 -83 -124 -67 0 277 1169 291 356 295 1170 296 653 883 402 1203 414 983 1210 299 756 1177 754 268 1416 1417 949 951 1518 142 601 1519 149 1501 975 143 1119 1145 168 170 1107 1513 0\n1521 135 44 -91 62 111 36 -83 -124 -67 0 402 1203 414 653 983 1210 805 899 898 1520 1101 1505 277 1169 291 356 295 1170 296 298 372 301 957 1501 1152 268 358 566 417 1205 390 119 98 1265 621 1488 1448 289 1502 1510 52 605 54 612 1103 300 1161 336 333 1369 278 81 69 1015 397 0\n1522 -282 -91 111 36 -83 -124 -67 0 298 1152 268 983 1210 805 899 898 1520 1101 566 417 1205 390 402 1203 1201 469 393 392 1510 0\n1523 -91 62 111 36 -83 -124 -67 0 983 1210 805 899 898 1520 1101 417 1205 390 277 1169 291 356 295 1170 296 653 402 1203 414 298 566 1152 268 1522 412 1502 1521 1510 1496 605 0\n1524 62 111 36 -83 -124 -67 0 983 1210 805 899 898 1520 1101 417 1205 390 800 896 795 895 653 402 1203 414 1523 513 168 568 1113 1119 138 1497 1510 392 1502 469 412 0\n1525 -62 140 -141 36 0 417 1205 390 273 1216 1156 293 1411 513 168 568 1113 951 138 0\n1526 36 -83 -124 -67 0 983 1210 800 896 805 899 898 1520 1101 417 795 895 1525 1524 394 1217 1187 411 1411 513 1415 568 0\n1527 -54 274 -83 43 0 291 1181 267 1020 376 410 299 463 1101 417 0\n1528 250 54 110 -83 -124 -67 0 983 1210 1526 163 1138 1140 98 1451 1139 137 561 402 425 1450 388 11 1019 0\n1529 -29 61 110 44 -83 -124 -67 0 983 1210 805 899 898 1488 402 1203 414 653 291 1170 296 277 1169 356 295 1526 1158 289 98 1265 621 140 1108 163 1139 180 148 1018 97 1138 1140 142 1022 1127 220 155 1493 392 1185 448 1527 1399 1184 416 883 1205 417 1101 756 754 513 1514 1487 1036 1001 1000 299 1157 561 1452 1181 303 543 1019 7 551 99 403 1208 1223 1283 659 122 0\n1530 61 110 44 -83 -124 -67 0 983 1210 1526 163 1138 1140 98 1451 277 1169 289 1265 621 140 1108 1139 180 148 1018 142 1127 220 155 137 561 291 356 295 1181 303 1170 296 653 883 402 1203 414 97 805 899 898 1488 151 1158 1493 1022 392 1185 448 1527 1399 1184 1205 416 417 1101 299 756 1452 1157 754 1000 1001 513 1514 1036 1487 1529 11 287 541 1167 266 984 551 99 403 1208 1223 1283 659 122 0\n1531 -102 29 110 -83 -124 -67 0 983 1210 1526 163 1138 1140 98 1451 140 1108 1139 180 148 142 1127 220 155 137 561 291 1181 303 1170 296 653 883 402 1203 414 1265 97 805 899 898 7 9 388 1017 551 1182 1196 1184 1205 99 404 450 1527 416 417 403 410 11 1101 1208 287 756 555 420 1155 754 272 1000 1001 513 1493 1530 1283 1036 600 122 107 659 0\n1532 -109 102 29 127 -83 -124 -67 0 1526 163 1139 137 561 402 983 1210 140 1108 1127 151 805 899 898 392 1213 1185 400 448 1527 11 287 541 1167 6 266 0\n1533 29 110 -83 -124 -67 0 983 1210 1526 163 1138 1140 98 1451 277 1169 289 1265 621 140 1108 1139 180 148 1018 142 137 561 291 356 295 1170 296 1181 653 119 402 1203 414 800 896 1193 97 805 899 898 1488 1448 1114 150 1531 1532 1493 47 49 987 11 267 1020 989 376 124 126 128 131 410 609 1152 299 465 908 907 298 1101 419 795 999 895 69 513 639 1514 86 0\n1534 -61 95 145 47 210 144 28 126 11 133 243 -67 0 303 983 1210 805 899 898 1488 1448 140 1128 152 570 277 1158 282 272 379 322 300 292 122 162 608 1137 1103 172 1044 107 0\n1535 110 -83 -124 -67 0 983 1210 140 1108 1526 163 1139 180 148 1138 1140 142 1127 220 155 291 1181 303 1170 296 653 883 402 1203 414 98 1265 97 805 899 898 1533 16 157 543 1019 1528 1132 7 388 1017 551 1183 1134 1182 1184 1205 99 410 141 404 416 417 403 1101 1208 299 756 555 420 1157 754 1000 1001 513 1036 1534 1493 1530 1283 600 122 107 659 0\n1536 -44 95 145 47 210 144 28 133 126 11 -110 96 -67 0 983 1210 140 1128 152 570 277 1158 282 1044 611 107 122 172 162 1137 0\n1537 -83 -124 -67 0 402 1203 414 98 1265 621 983 1210 805 899 898 1488 140 1108 1127 277 1169 289 291 883 653 1170 1181 356 296 303 295 1526 163 561 1138 1139 220 1140 137 180 155 142 148 1018 1535 48 52 393 1215 991 1186 1527 11 157 1019 1132 388 1017 551 1134 1182 1184 1205 99 141 404 450 416 417 403 410 1101 1208 299 756 555 420 1157 754 1000 1001 513 1514 1036 1536 1223 172 659 1137 122 162 0\n1538 -35 29 78 54 -92 127 0 162 565 1112 11 137 0\n1539 46 44 -84 -26 210 28 -91 126 83 -67 0 292 1171 302 654 983 1210 140 1128 154 216 158 298 324 273 805 899 898 1488 1448 277 1158 107 1228 286 1209 348 409 300 509 1103 161 418 612 1066 233 1206 392 588 164 394 1197 406 1407 393 604 1201 54 412 0\n1540 44 -84 -26 210 28 -91 126 83 -67 0 292 322 272 983 1210 140 1128 154 216 158 298 324 273 1382 1449 1265 805 899 898 1488 1448 152 570 277 1169 289 1158 282 1539 172 665 1147 155 218 161 1106 409 1396 1198 1209 285 345 318 294 371 271 300 1103 418 612 606 1206 483 394 393 1260 148 1141 244 164 54 412 590 469 35 392 0\n1541 -135 60 -76 284 -67 0 983 1210 140 1128 152 570 277 1158 282 412 590 469 35 392 0\n1542 -76 284 13 111 209 186 -67 0 273 983 1210 140 1128 152 570 277 1158 282 285 345 318 294 271 1541 54 164 594 245 35 141 0\n1543 159 54 -44 145 96 47 -26 -92 -67 0 983 1210 140 1108 1127 154 215 157 1128 216 96 1449 620 277 1169 289 142 188 918 148 0\n1544 -86 88 -132 54 -44 145 96 47 29 39 177 31 129 -92 -67 0 409 1198 414 983 1210 140 170 1145 189 149 277 1169 289 602 1501 918 631 0\n1545 87 69 118 76 137 88 20 39 -67 0 935 936 99 0\n1546 133 -26 35 28 -92 126 83 -67 0 983 1210 140 1108 1127 154 215 157 96 1463 166 1128 216 1449 620 97 299 1157 277 1169 289 1353 1381 133 298 125 127 129 292 1540 324 1151 170 617 273 267 1145 1230 143 189 1148 149 161 1106 409 1032 1198 414 1542 1543 1140 164 952 1544 54 412 577 1190 442 397 1545 295 631 1174 1007 0\n1547 -26 35 -92 -102 83 -67 0 299 1177 555 388 1196 405 1182 404 983 1210 140 1108 1127 154 544 215 157 1546 410 563 1183 389 11 267 1172 293 370 298 1416 1417 1461 0\n1548 -54 -75 5 104 6 91 202 274 83 -67 0 1353 410 1183 389 268 983 1210 805 899 898 18 267 1172 293 1461 1460 1133 1028 1477 513 1093 416 1184 0\n1549 91 26 -92 -102 83 -67 0 299 1177 1157 388 1196 405 1182 983 1210 805 899 898 1488 1448 140 1128 152 570 277 1158 282 1416 1417 1353 410 563 1183 1199 450 389 420 402 1105 284 545 1548 11 287 1262 1155 142 607 317 1294 271 170 1103 418 1072 482 1376 392 1115 35 141 0\n1550 26 -92 -102 83 -67 0 983 1210 1549 893 1382 787 505 894 791 0\n1551 -92 -102 83 -67 0 388 1196 405 983 1210 140 1108 1127 299 1550 154 544 1547 215 124 157 1353 1538 298 267 370 1172 0\n1552 -103 176 55 6 251 83 0 390 389 428 409 509 161 1362 232 163 0\n1553 -5 133 -141 83 0 1353 137 562 1112 1381 162 0\n1554 -26 5 202 6 251 -102 83 169 0 268 390 388 1196 405 154 544 215 157 1552 11 1461 267 293 1172 0\n1555 -54 133 -141 83 0 1353 267 564 1151 1381 292 0\n1556 -36 88 137 39 251 -102 169 0 163 1017 220 155 0\n1557 -102 83 -67 0 983 1210 805 899 898 1488 1448 140 1108 1127 277 1158 388 1196 1551 1101 417 1205 463 390 426 410 403 1353 298 1382 566 1152 1463 268 166 1553 1554 505 402 1009 1203 509 414 467 652 411 1556 1411 949 293 550 1156 99 285 1542 1165 345 55 57 612 295 371 1496 1103 300 0\n1558 -182 -78 133 -91 -124 103 54 83 -67 0 983 1210 570 1557 140 1108 1127 151 1128 152 277 1158 282 287 1167 266 1307 541 984 1215 805 899 898 791 894 893 787 1101 98 97 1114 1117 208 1494 148 0\n1559 -76 109 28 -124 -34 -85 102 -67 0 402 1203 161 1136 293 1156 1217 1542 1465 0\n1560 -78 133 -91 -124 103 -34 54 259 83 -67 0 983 1210 805 899 898 791 894 893 787 1101 98 97 161 1148 1557 140 1108 1127 151 1128 152 570 277 1158 282 1169 287 1215 541 1155 1167 272 266 984 1558 162 1381 292 361 301 1261 1493 974 300 1359 348 0\n1561 133 -91 27 -124 -34 -85 259 83 -67 0 1557 983 1210 805 899 898 791 894 893 787 1101 1479 402 1203 414 652 1019 98 161 1136 166 1148 560 293 1172 267 1488 277 1169 1553 1560 11 405 1186 393 432 1451 392 1117 257 1559 162 170 1011 99 1381 1395 665 292 1171 361 302 301 107 1386 0\n1562 -231 77 44 46 144 28 -141 -67 0 277 1169 1171 361 302 301 107 1386 0\n1563 -94 44 61 109 110 -133 -141 243 -124 -67 0 98 1265 621 97 277 1169 289 301 637 382 1493 278 972 69 1189 397 0\n1564 -78 136 38 109 110 -133 -91 -124 -34 62 111 -67 0 402 1193 410 465 419 1183 983 1210 805 899 898 791 894 893 787 1101 298 1176 666 98 1265 621 97 161 1148 173 1488 1448 140 1114 150 277 1169 289 287 1450 1155 1140 257 272 164 170 908 907 1563 957 86 171 260 148 1493 981 42 954 0\n1565 -12 87 19 20 136 38 145 -91 -124 47 62 111 -67 0 983 1210 805 899 898 791 894 893 787 1101 98 1265 621 277 1169 42 142 954 1140 164 0\n1566 -37 -125 109 186 -67 0 983 1210 140 1128 152 570 277 1158 282 164 592 245 35 141 0\n1567 19 20 37 136 38 109 110 -91 -124 -34 62 111 -67 0 983 1210 805 899 898 791 894 893 787 1101 666 98 1265 621 97 161 1148 173 277 1169 289 981 1565 954 1493 47 0\n1568 94 37 136 38 109 143 110 -91 -124 -34 62 111 -67 0 983 1210 805 899 898 791 894 893 787 1101 161 1148 1488 1448 140 1114 150 957 1567 148 188 260 257 171 170 908 907 86 0\n1569 -91 27 -124 -34 62 -85 259 83 -67 0 402 1203 414 983 1210 791 894 1193 98 1265 652 621 161 1136 166 1217 1557 805 899 898 1488 1448 140 277 1169 289 298 893 1176 787 1101 1479 1561 410 450 437 465 434 393 419 392 1559 99 403 625 1194 413 1566 1568 301 637 382 1567 278 149 69 1146 397 255 1189 170 464 1563 418 272 1103 379 300 0\n1570 91 -124 103 -34 54 62 111 259 83 -67 0 402 1203 1193 652 98 97 161 1136 166 1148 983 1210 805 899 898 1028 1488 1448 140 1114 150 979 1353 513 410 437 465 393 419 1452 257 170 908 907 1513 1092 148 637 260 86 171 0\n1571 94 70 119 -19 -141 -91 276 194 83 -10 0 148 260 171 140 1114 208 162 150 1261 86 1381 419 410 465 0\n1572 -19 -141 -91 276 194 83 -67 0 983 1210 805 899 898 1488 1448 140 1114 277 1169 148 188 208 257 162 170 908 907 1571 301 637 361 1381 292 0\n1573 -94 37 38 136 -91 -124 -34 62 111 259 83 -67 0 161 1148 402 1193 983 1210 805 899 898 791 894 893 787 1101 1572 298 1176 98 1265 621 1488 1448 140 277 1169 289 301 361 382 292 278 69 397 640 1189 1381 410 450 437 464 434 393 418 392 1567 149 1146 255 170 1103 1563 300 272 379 0\n1574 -124 -34 62 -85 259 83 -67 0 161 1148 173 560 293 1172 267 1217 1557 983 1210 805 899 898 140 1128 277 1169 289 97 98 402 621 791 1019 1265 1193 894 1570 893 666 1569 787 155 624 1101 1130 221 165 164 1572 981 1573 957 954 1565 47 48 1493 392 1185 432 448 437 405 410 1553 1560 11 0\n1575 -141 94 136 87 19 38 37 30 31 129 145 -91 47 62 111 -67 0 983 1210 277 1169 954 957 0\n1576 -35 -92 30 -173 31 129 54 102 -67 0 983 1210 140 1108 1127 215 157 277 1169 289 162 1112 1340 182 1538 1010 287 266 1167 0\n1577 94 136 87 19 38 37 177 -26 145 -91 194 54 62 111 83 -67 0 154 262 172 983 1210 140 1108 1127 215 157 158 298 1176 303 1382 1449 1265 173 1557 805 899 898 1488 1448 1128 152 1114 150 570 277 1169 289 1158 1487 1575 1101 299 1230 1157 908 907 1038 1576 923 1546 0\n1578 -92 142 -133 79 128 29 177 96 31 129 145 194 54 259 -67 0 410 158 173 983 1210 805 899 898 1488 1448 277 1169 289 1230 563 1103 964 607 0\n1579 19 -26 -91 -34 54 62 111 259 83 -67 0 161 154 1129 234 165 980 233 164 983 1210 140 1108 1127 215 157 158 298 1176 303 1382 1449 1265 666 1148 173 805 899 898 1488 1448 277 1169 289 1018 981 955 1577 301 361 382 292 278 69 397 574 640 1189 1381 410 437 464 393 418 1578 1101 954 149 1146 255 170 972 1103 41 300 272 379 0\n1580 -133 -141 44 -19 46 -26 102 -67 0 1479 983 1210 805 899 898 1488 140 1108 1127 151 410 655 637 1199 1386 420 927 286 1395 1150 1418 266 0\n1581 -141 -19 -26 -91 194 83 -67 0 983 1210 140 148 188 257 170 1114 208 162 154 262 172 1557 277 1169 1580 1381 292 1261 361 301 0\n1582 -84 70 119 45 -19 -67 0 983 1210 140 1114 150 277 1169 292 636 361 86 301 0\n1583 -91 124 -34 54 62 111 259 83 -67 0 161 1148 983 1210 805 899 898 1488 1448 140 1114 1382 1105 154 262 172 1579 148 188 208 260 257 162 171 170 908 907 1581 1101 299 1157 1582 1381 410 655 637 1199 1487 1223 0\n1584 -19 -26 -133 194 102 -67 0 154 262 172 655 410 1199 983 1210 805 899 898 1488 140 148 637 188 1487 257 170 1580 1223 1101 1157 299 0\n1585 -26 -140 -133 -34 62 111 102 -67 0 410 1199 161 1148 983 1210 805 899 898 1488 1448 140 1114 150 277 1169 289 1158 96 154 620 980 1449 1129 262 233 234 172 164 165 1584 981 955 1447 1053 93 94 628 1038 927 286 348 300 1071 65 418 1395 482 392 0\n1586 -75 39 62 112 111 -67 137 -140 0 1480 1487 1486 0\n1587 -34 62 -85 259 83 -67 0 293 1172 267 1217 1557 983 1210 805 899 898 1488 161 1028 1136 166 1574 1583 1353 513 1585 505 1374 1586 0\n1588 -75 103 137 5 39 88 201 62 111 259 83 -67 0 267 1557 983 1210 805 899 898 1488 140 1108 1127 151 1128 152 570 277 1158 282 96 284 1382 1586 1175 340 307 1353 1107 367 288 266 410 657 168 295 1010 1307 1199 437 1113 1514 157 393 183 1487 1492 155 1101 1036 299 1157 1223 170 609 1294 142 1262 1225 11 1044 1325 1423 35 598 0\n1589 -44 19 194 110 -133 30 31 129 -67 0 277 1169 289 983 1210 170 609 257 1260 142 0\n1590 94 44 46 -133 -26 102 -67 0 983 1210 805 899 898 1448 1488 907 908 410 1199 420 655 140 1108 1127 151 1114 150 1487 1223 1038 1157 927 299 286 1395 1101 1150 1418 266 0\n1591 -42 -133 -26 186 31 129 5 -132 54 111 259 55 104 6 102 -67 0 410 437 393 983 1210 140 1108 1127 154 215 157 1128 216 158 409 1198 414 1009 1033 1032 277 1169 289 168 1119 1143 252 143 1584 172 1018 1589 1590 1514 295 1174 278 69 397 574 1189 1087 964 460 142 412 975 0\n1592 -117 128 44 -133 29 30 5 54 259 -67 0 410 983 1210 805 899 898 1488 1448 397 574 1189 964 464 607 418 1103 0\n1593 19 44 -91 -133 -26 186 31 129 284 5 39 88 298 54 209 111 259 102 -67 0 298 1176 410 983 1210 140 1108 1127 154 215 157 1128 216 158 414 805 899 898 1488 1448 1220 277 1169 289 1018 1592 1006 278 1159 382 288 301 964 1590 607 172 665 1103 1147 612 155 1542 99 0\n1594 44 -91 -133 -26 186 31 129 284 5 39 88 298 54 209 111 259 102 -67 0 298 414 983 1210 805 899 898 1488 1448 277 1158 1593 637 1590 172 665 1147 155 99 285 1542 345 612 371 1103 300 0\n1595 -19 20 76 13 -132 62 111 55 104 6 -67 0 409 1198 414 1009 1033 1032 983 1210 140 148 631 1141 188 1501 244 975 164 577 952 1545 0\n1596 -133 140 -26 186 31 129 5 -132 54 209 62 111 259 55 104 6 102 -67 0 983 1210 140 1128 154 216 158 409 1198 414 1009 1033 1032 852 1220 277 1169 289 410 437 393 1591 513 1594 170 609 1145 143 189 1542 149 1595 1260 142 602 1140 975 164 412 577 952 1190 1545 442 295 397 1174 1006 278 0\n1597 -117 -159 13 128 29 30 103 5 -132 54 111 55 104 6 -10 0 409 397 574 1189 460 412 975 602 987 991 11 0\n1598 12 79 128 29 30 103 5 54 0 987 991 11 0\n1599 -159 76 13 128 19 -91 133 -26 103 5 -132 54 62 111 55 104 6 -67 0 983 1210 140 1108 1127 154 215 157 1128 216 158 409 1198 414 1009 1033 1032 852 805 899 898 1488 1448 1220 1117 1140 162 164 1380 952 292 1597 1006 278 1159 1174 288 360 295 300 1598 606 602 1103 54 170 577 1145 1545 189 149 0\n1600 159 128 -173 75 250 5 54 -67 0 983 1210 140 1108 1127 215 157 1128 216 158 1265 389 142 1391 1598 11 52 1450 0\n1601 12 19 29 30 31 129 103 5 54 -67 0 983 1210 277 1169 289 1018 1598 49 52 1260 0\n1602 13 -159 128 19 -91 133 -26 186 103 5 -132 54 209 62 111 55 104 6 -67 0 409 1198 1542 1599 0\n1603 19 -91 133 186 75 250 5 -132 54 209 62 111 55 104 6 -67 0 983 1210 140 1108 1127 1009 1105 154 215 157 1128 216 158 1449 1265 389 409 1209 805 899 898 1488 1448 1114 150 277 1169 289 1018 1600 1117 162 1380 1601 1602 143 1145 170 908 1235 0\n1604 -13 -84 -19 -91 -132 -67 0 631 298 409 1198 414 1009 1033 1032 983 1210 805 899 898 1488 1448 143 612 1145 170 908 907 1103 1582 300 171 647 1161 1146 336 149 1369 0\n1605 133 75 250 5 -132 54 209 62 111 55 104 6 83 -67 0 983 1210 140 1128 1009 1105 154 216 158 1463 409 1209 1198 805 899 898 1488 1114 277 1169 1353 1603 148 208 162 1380 292 361 301 1487 1604 1542 1595 149 957 1146 1101 255 299 1546 170 1157 111 1228 0\n1606 -85 259 55 251 104 6 83 -67 0 1557 983 1210 805 899 898 1488 1448 140 1108 1127 1128 277 1169 289 27 293 1217 951 1156 1172 267 1587 1106 409 884 1009 1032 1033 557 1198 1209 428 414 421 389 1588 1265 1449 1463 1105 154 216 215 158 157 1605 126 130 410 1596 437 133 758 393 762 1101 299 1452 1157 1140 1078 164 1084 1519 1513 982 149 1544 1542 952 1545 54 577 0\n1607 -183 110 -26 186 75 250 54 102 -67 0 983 1210 140 1108 1127 154 215 157 389 1138 1139 985 1140 137 542 1450 11 0\n1608 159 -134 110 -91 -133 62 111 75 -132 102 -67 0 298 1176 1152 410 1199 983 1210 140 1128 1009 1105 154 216 158 1449 1265 409 1198 414 1033 1032 852 805 899 898 1488 1448 1108 1127 151 152 570 1220 277 1169 289 1158 282 142 188 191 148 141 1018 1260 49 272 603 609 1087 379 300 1103 418 612 1191 482 54 443 392 397 35 1006 1086 278 665 382 1590 301 0\n1609 -68 76 69 44 118 -91 -133 -132 -67 0 983 1210 805 899 898 1448 1488 907 908 298 1176 409 1198 414 1009 1033 1032 140 1114 150 278 639 1174 382 295 301 1545 86 642 0\n1610 135 44 13 -159 110 -91 -133 62 55 111 75 -132 104 6 -67 0 983 1210 805 899 898 1448 1488 907 908 298 1176 133 140 1128 1009 1105 154 216 158 1449 1265 1114 150 277 1169 289 1158 975 1504 294 602 272 345 1260 285 637 1595 149 642 1146 86 171 0\n1611 -135 20 118 13 -134 -91 62 111 -132 102 -67 0 30 25 298 1152 268 1009 121 1382 1105 409 1198 414 1033 1032 852 983 1210 1220 412 577 1190 469 442 392 397 1466 1595 1545 1006 295 278 1174 0\n1612 -44 13 -134 -91 -133 62 111 -132 102 -67 0 121 1382 409 411 1187 436 393 1608 1140 164 983 1210 952 30 25 140 1128 1009 1105 154 216 158 298 1152 268 1449 1265 1198 414 1033 1032 277 1169 289 170 609 1145 189 149 1611 975 602 1501 1260 631 0\n1613 13 -134 -91 -133 62 111 -132 102 -67 0 121 1382 409 411 1187 436 393 1608 1140 164 30 25 298 1152 268 1449 1265 1198 983 1210 805 899 898 1488 1448 140 1114 150 277 1169 289 952 1612 908 907 1610 412 577 1611 1190 469 149 642 442 392 1146 397 1466 171 1609 86 69 637 0\n1614 -134 -91 -133 62 111 -132 102 -67 0 983 1210 140 1128 1009 121 1382 1105 154 216 158 298 1152 268 1449 1265 1176 133 409 1198 414 1033 1032 805 899 898 1488 1448 277 1169 289 1158 25 30 411 1187 436 393 1608 1613 57 143 612 1504 1145 272 170 1103 300 607 348 1260 347 637 285 1590 172 665 1147 99 155 0\n1615 -46 76 -91 137 39 88 0 172 665 1147 99 155 0\n1616 -133 -13 134 -91 -132 102 -67 0 1009 1032 1033 409 1198 414 298 277 1158 983 1210 805 899 898 1448 612 1488 143 1145 170 1103 300 348 347 285 1615 1176 379 272 1118 163 140 1108 1127 121 1382 1105 154 215 157 1128 216 158 1449 1265 1169 289 410 607 1590 1183 637 389 1018 1260 52 1215 991 1062 1411 1101 299 563 376 1601 267 0\n1617 -94 133 -91 -132 -67 0 1009 121 1382 1105 298 1176 852 983 1210 140 1114 1220 277 1169 301 361 382 292 278 1380 162 640 208 1006 148 0\n1618 -13 134 -91 -132 102 -67 0 983 1210 140 1128 1009 121 1382 1105 154 216 158 1449 1265 298 1176 409 1198 414 1033 1032 805 899 898 1488 1448 1114 150 277 1169 289 1158 143 612 1145 170 908 907 1103 300 348 379 286 347 272 285 1011 1615 1616 1617 1487 1038 107 302 1171 292 1380 162 610 1117 208 142 148 1260 0\n1619 -35 19 94 -26 -132 -67 0 983 1210 140 1128 154 216 1129 409 1209 852 805 899 898 1488 1448 1114 150 1220 162 237 238 170 171 908 907 86 1030 638 1006 0\n1620 44 19 133 -91 -132 -67 0 1009 121 1382 1105 1617 1619 1380 292 1151 267 983 1210 805 899 898 1488 1487 140 1108 1127 154 215 157 1128 216 158 298 1152 268 1449 1265 409 1209 1448 1114 150 277 1169 908 907 1235 1038 1546 1101 417 566 1553 1205 1552 1601 0\n1621 -141 5 20 54 13 111 110 19 -91 -132 -67 0 983 1210 277 1169 289 121 1382 1265 1449 1018 140 1108 1127 1009 1105 154 215 157 1128 216 158 298 1152 268 1463 409 1209 1557 417 566 1188 1205 480 1552 390 1600 1607 1601 1606 1140 163 602 22 164 951 54 952 1611 0\n1622 -92 19 133 -91 -132 -67 0 983 1210 140 1620 170 1145 189 149 1009 121 1382 1105 1617 1619 1380 292 1151 267 143 1171 617 805 899 898 1488 1487 1108 1127 154 215 157 1128 216 1449 1265 133 1002 671 298 409 1209 421 1557 1033 1032 151 152 570 277 1169 289 1158 282 299 1543 1544 918 1546 1157 375 1140 553 598 324 266 164 273 984 54 35 412 141 1190 192 1367 155 0\n1623 19 133 -91 -132 -67 0 1617 1009 121 1382 1105 983 1210 805 899 898 140 1619 1620 1380 170 611 617 292 1145 1151 143 189 267 149 1622 1101 1553 1621 0\n1624 -141 -44 -19 -91 -132 -67 0 983 1210 140 170 1145 189 149 143 617 1108 148 1141 241 163 244 164 631 298 1152 268 133 409 1198 414 121 1557 1009 1033 1032 417 566 1525 1496 1188 1205 952 1611 390 1411 1606 0\n1625 -44 -19 -91 -132 -67 0 983 1210 140 148 1141 244 164 631 121 1382 1463 298 409 1198 414 1009 1033 1032 805 899 898 170 617 1145 143 189 149 1501 1624 1101 299 1157 324 273 1542 54 952 1545 577 0\n1626 46 210 -19 -91 -132 -67 0 1625 983 1210 140 1114 148 208 162 1128 1009 121 1382 1105 154 216 158 409 1209 1557 805 899 898 1488 1228 1380 1590 637 0\n1627 210 -19 -91 -132 -67 0 1625 983 1210 140 148 1141 244 164 298 409 1198 414 1009 1033 1032 805 899 898 1488 1448 277 1158 324 273 1626 1615 285 345 318 371 271 300 1103 294 1541 418 612 54 1206 394 0\n1628 -19 -91 -132 -67 0 298 1152 268 133 409 1198 414 121 1557 1009 1033 1032 983 1210 805 899 898 140 1114 1108 148 631 1141 188 208 244 241 162 164 163 1627 1157 299 1101 417 566 1525 1188 1205 390 1606 22 949 1614 1617 1380 957 1604 1501 975 952 1611 0\n1629 -36 110 -91 -132 -67 0 1628 1623 410 1183 1009 121 1382 1105 1463 1557 163 559 1607 0\n1630 -141 -91 -132 -67 0 1628 1623 410 298 1152 268 133 121 1557 417 566 1188 1205 437 390 393 1606 1629 1525 22 1614 949 0\n1631 -134 -91 -132 -67 0 1628 1623 983 1210 805 899 898 1630 1101 563 410 1183 389 121 1382 1265 1449 140 1128 1009 1105 154 216 158 1108 1127 215 157 298 1176 299 376 267 1601 45 1629 1157 324 273 1152 268 1557 25 30 1614 949 0\n1632 -111 93 -91 43 0 1488 1448 394 617 1206 1103 418 0\n1633 -91 -132 -67 0 409 1198 414 121 1557 1009 1033 1032 852 120 983 1210 805 899 898 140 1108 1127 1128 1220 277 1169 289 133 298 1382 1176 1265 1449 1463 1105 154 216 215 158 157 1628 1018 1623 410 1183 389 1630 1101 299 563 1157 376 324 267 273 1600 1601 1140 607 602 164 1631 1618 1632 54 952 1542 412 577 1190 442 397 1006 1007 1609 1174 170 295 1145 1545 189 149 0\n1634 -132 28 -67 -140 36 -194 110 61 43 91 0 983 1210 121 1009 1320 1557 1271 1265 1105 1101 154 1279 0\n1635 -67 62 -12 61 -191 43 111 91 0 142 1140 250 168 1107 1109 1139 163 1145 195 161 164 257 45 143 277 983 1169 1210 140 1128 189 224 149 156 1634 509 291 1410 1537 601 1170 356 1105 54 296 295 154 648 1501 1142 166 0\n1636 -10 186 137 88 67 -140 37 -44 43 144 111 0 166 615 65 64 1488 1448 1220 848 1104 147 1050 247 950 948 165 1071 0\n1637 -26 -83 67 -140 37 -44 43 144 111 0 291 1170 296 886 895 154 648 1142 1636 1102 797 767 690 1101 768 865 1104 0\n1638 -83 67 -140 -12 -44 43 144 111 0 615 170 1145 142 195 161 1140 164 143 65 64 1488 1448 291 601 54 294 1160 279 332 278 1637 977 1104 997 505 284 871 1164 718 356 1210 295 140 952 189 149 921 1004 148 630 1141 1071 165 0\n1639 -12 61 -44 43 144 111 91 0 170 1145 142 1140 195 250 161 168 1107 615 1635 1638 1315 1268 1106 1210 1220 848 1104 1439 847 1311 849 0\n1640 -140 298 83 67 0 1315 1210 1220 848 1104 1439 847 850 849 505 0\n1641 -10 178 129 -75 159 6 -132 83 12 -44 43 91 0 159 284 1164 289 1353 410 1183 389 609 140 1108 188 229 227 148 158 157 1018 1263 1260 52 393 943 991 1186 1188 1062 417 1101 299 563 1417 1177 1461 0\n1642 -60 -141 95 28 22 -75 -133 -44 0 410 1199 417 479 388 271 1212 598 1154 1423 281 286 552 6 1150 266 0\n1643 26 83 67 12 -44 43 91 0 1268 1640 513 1028 1106 409 1198 414 170 168 1143 257 1113 138 1126 211 1353 609 410 977 1311 1104 98 284 618 651 147 1032 1164 1120 1121 1135 204 203 151 152 156 155 1036 1641 1102 270 571 1240 1163 351 1101 282 288 417 1188 437 393 1225 1642 35 392 589 1197 41 406 0\n1644 -109 28 259 46 95 144 -44 0 392 600 434 107 404 0\n1645 -23 67 0 152 1121 1128 147 140 501 1102 572 0\n1646 -177 -26 -132 0 154 1129 1123 229 1314 140 867 699 1102 697 0\n1647 -59 -141 -26 -451 -42 67 0 690 759 865 763 501 0\n1648 -296 297 67 0 848 847 1104 0\n1649 83 67 12 -44 43 91 0 1268 1640 513 1028 1106 884 1643 849 1648 1220 1102 1240 1647 1101 0\n1650 -26 -59 -83 67 43 91 0 869 690 710 865 501 930 712 904 1107 903 895 1101 797 0\n1651 -59 -83 67 43 91 0 119 718 871 1650 977 1105 1104 997 0\n1652 133 103 78 19 -141 80 129 35 29 30 31 -10 145 47 -83 12 -44 43 0 291 1181 303 1020 122 611 562 1260 11 1214 0\n1653 -140 -141 -75 -18 -10 145 47 -83 12 -44 43 0 417 1188 284 1164 289 618 170 140 255 147 1135 238 162 1108 227 157 229 158 159 416 1421 1204 1018 1263 480 389 1652 609 943 1260 52 0\n1654 -141 26 67 12 -44 43 91 0 1649 1651 1210 1220 1648 850 1105 284 1164 289 848 1104 618 170 140 255 147 1135 238 162 1108 227 157 229 158 159 291 1181 303 1001 1000 119 417 1188 1653 513 168 568 1113 1143 138 260 944 148 1004 1018 1263 278 1159 288 943 991 122 1413 611 1155 1260 272 0\n1655 26 67 12 -44 43 91 0 1649 1651 1210 140 1108 1220 848 1104 147 1135 227 157 229 159 1648 850 291 1181 303 1001 1000 65 64 1488 1448 1105 284 618 1164 289 356 295 1654 1101 299 1416 1417 1177 376 268 267 918 1230 148 630 1143 1141 168 165 244 241 1107 164 163 615 1071 949 0\n1656 67 12 -44 43 91 0 170 1145 65 64 1488 1448 1649 291 1170 296 1651 1210 140 1220 1108 255 189 848 1104 147 203 187 259 179 155 1655 154 648 1142 166 247 245 252 242 950 948 165 164 168 163 1107 416 615 1071 1184 394 390 1187 473 417 1101 299 1416 1177 949 268 0\n1657 -92 -83 12 -44 43 91 0 1656 983 1210 140 1108 1127 1537 1410 505 154 215 157 1128 216 277 1169 291 356 295 1181 303 1449 1265 1001 1000 289 65 64 1488 1448 299 1416 1417 1177 376 268 267 918 1230 1543 148 630 1143 1109 1140 1141 168 1139 164 165 1107 163 615 1071 949 0\n1658 19 54 110 103 -141 35 29 30 96 31 129 145 47 -67 12 -44 0 277 1169 289 983 1210 1260 1601 609 562 122 0\n1659 -19 111 62 -83 20 -67 13 0 983 1210 140 148 1368 1141 164 244 0\n1660 -140 -141 145 47 -83 -67 12 -44 43 0 417 1188 170 983 1210 140 1128 224 1537 1410 505 154 219 162 1108 1127 215 157 216 158 1142 166 648 291 1181 303 1449 1265 1145 189 149 277 1169 289 143 416 615 1204 439 480 394 389 1497 1659 1260 1658 609 1020 0\n1661 -83 12 -44 43 91 0 170 1656 983 1210 140 1128 224 1108 1127 255 277 1169 289 291 1410 1537 1000 1001 1181 1265 1449 505 303 154 216 215 219 158 157 162 1657 1101 417 1393 1188 1660 513 168 568 1113 1143 138 260 944 148 1018 69 278 1159 288 943 987 122 611 1413 1260 1155 272 0\n1662 -30 -141 12 -44 43 91 0 417 1188 1661 1656 983 1210 1220 33 1276 1353 410 1199 420 170 140 1128 224 152 570 277 1158 282 1488 158 1134 216 141 154 1105 1374 1492 589 301 35 1166 598 286 1375 509 161 1028 1136 1107 166 416 615 1586 439 394 0\n1663 -31 -141 12 -44 43 91 0 1662 1661 1353 410 417 1188 437 393 170 1656 983 1210 140 255 1271 260 148 1220 33 1276 1199 420 609 1268 1128 224 152 570 277 1158 282 1488 73 74 1449 1006 284 1374 1492 1225 340 301 288 1166 943 286 406 1197 392 35 598 1375 509 161 1028 1136 1107 166 416 615 1586 439 394 0\n1664 -141 12 -44 43 91 0 1661 1353 410 1199 420 609 170 1656 983 1210 140 1128 224 152 255 570 1220 277 1169 289 1158 282 1488 33 417 1271 1276 1188 260 437 148 393 1662 1663 1260 620 1265 1225 284 1374 1492 340 301 288 1166 943 286 406 1197 392 35 598 1375 509 161 1028 1136 1107 166 416 615 1586 439 394 0\n1665 110 30 -129 12 -44 43 91 0 1656 277 1265 284 1175 367 295 1158 340 288 296 1661 1374 98 620 1664 1101 299 1177 268 1157 1416 1353 410 1199 420 609 1557 170 983 1210 140 1128 224 156 152 570 282 1488 1225 41 1044 406 1197 392 35 598 1375 1423 509 161 1028 1136 1107 166 1459 1067 1474 0\n1666 30 -129 12 -44 43 91 0 1656 277 1158 1265 284 340 288 1175 296 1661 1374 98 72 1664 1101 299 1177 268 1353 563 1417 1416 410 1183 389 1557 983 1210 140 1108 1127 151 1128 152 570 282 1665 53 393 1186 1548 1427 157 1307 266 1298 308 363 1106 285 293 409 1033 1305 459 99 411 549 22 0\n1667 -129 12 -44 43 91 0 1664 1101 299 1177 268 1157 1416 1661 1353 410 1199 420 609 1656 1557 170 983 1210 140 1128 224 156 152 570 277 1158 282 1488 620 1265 98 284 1374 1175 296 367 295 1666 48 589 1225 35 1044 598 1375 1423 509 161 1028 1136 1107 166 1459 1067 1474 0\n1668 -75 -30 12 -44 43 91 0 1656 983 1210 140 1128 152 570 277 1158 282 1664 1101 299 1157 158 1134 141 1044 1177 268 1416 1661 1353 410 1199 420 1557 170 224 156 1488 98 284 1374 589 1175 35 296 367 598 295 1375 1423 509 161 1028 1136 1107 166 1459 1067 1474 0\n1669 -30 12 -44 43 91 0 1664 1101 299 1177 268 1417 1416 1661 1353 410 1183 389 1656 1557 983 1210 140 1108 1127 1128 170 1145 48 158 216 154 1668 1463 505 166 402 1009 1203 509 414 161 652 195 1452 1477 163 1443 220 985 155 266 99 308 285 0\n1670 -124 75 30 129 202 5 104 6 103 83 167 -67 12 0 1463 166 1449 268 1557 983 1210 140 1108 1127 402 1009 1019 1203 509 414 161 652 207 148 1601 1477 163 1443 220 985 155 266 99 308 285 0\n1671 -34 176 177 31 129 104 6 -92 145 96 47 80 -10 -44 0 157 299 1177 268 161 1148 232 1230 163 1477 0\n1672 -54 -132 -26 31 30 129 202 5 104 6 61 83 -67 12 43 91 0 983 1210 140 1108 1127 154 215 157 1353 410 1183 389 1557 277 1169 289 18 20 1091 1062 513 1461 168 1186 1143 393 1584 1260 0\n1673 75 12 -44 43 91 0 1669 1667 1664 1101 299 1177 1661 1353 563 1417 1416 410 1183 389 609 131 130 126 1656 1557 170 983 1210 140 1128 224 156 1108 1127 1145 189 277 1169 289 1449 1670 1105 154 216 215 157 1671 1106 1672 918 1543 1230 1109 1143 1139 168 163 1107 1278 0\n1674 29 54 12 -44 43 91 0 1656 277 1673 284 1175 367 295 983 1210 140 1664 1101 170 1661 1294 188 148 1158 340 288 296 1262 1374 98 1669 299 1177 268 1157 1353 563 1416 410 1199 420 1183 389 1557 1128 224 156 152 570 282 1488 1427 11 585 1325 1044 35 598 1375 1423 509 161 1028 1136 1107 166 1459 1474 1067 0\n1675 -176 12 -44 43 91 0 1673 284 1175 296 1661 1374 98 1664 1101 299 1177 268 1157 1417 1416 1353 410 1199 420 1656 1557 983 1210 140 1108 1127 151 170 1128 224 152 570 277 1158 282 1132 1307 1134 266 1298 141 308 363 1106 1044 285 293 1033 1375 1305 598 99 35 549 1403 0\n1676 12 -44 43 91 0 170 1656 277 983 1158 1210 282 140 570 1128 152 224 1661 1353 410 609 1199 420 1664 1101 299 1416 1417 563 1157 1177 268 1669 1673 96 98 284 340 288 1675 157 1674 1548 1186 393 1225 41 1044 406 1197 392 35 598 1375 509 161 1477 232 163 0\n1677 -111 -44 43 91 0 170 1676 142 1140 250 168 1107 416 1184 390 1109 1139 163 394 1187 473 417 1101 299 1416 1177 949 268 0\n1678 -44 43 91 0 170 1145 143 1676 43 142 1117 1140 162 164 250 168 1107 416 615 1204 421 1677 1639 1635 109 114 420 1199 487 410 402 1353 291 1000 601 1651 1181 54 1210 303 294 578 140 1220 1384 1160 189 848 505 279 332 149 1104 284 618 278 147 1164 1135 289 356 159 295 921 69 148 630 1141 76 165 0\n1679 -83 75 62 111 160 -12 67 43 91 0 143 142 1140 164 291 601 1651 1170 54 1210 296 294 578 140 1220 1160 189 848 1648 279 149 1104 850 147 1105 203 154 648 155 1142 166 247 948 950 165 76 0\n1680 83 -140 67 91 0 1268 1640 0\n1681 -26 144 111 27 28 -18 -10 -83 -140 37 43 0 147 291 1170 296 1488 1448 154 648 1142 166 247 948 950 1051 165 1447 0\n1682 -111 36 43 91 0 1678 1488 1448 394 1187 1206 418 1103 616 1107 416 1184 473 390 417 1101 299 1416 1177 949 268 0\n1683 -75 -84 -18 -10 145 47 -83 -140 111 -12 44 112 63 0 292 1171 302 140 1114 147 204 156 1135 159 150 908 291 1181 303 416 1204 142 1140 164 1117 162 284 618 1164 356 1235 295 148 960 630 1141 1447 165 0\n1684 -84 124 -18 -10 145 47 -83 -140 111 -12 44 43 0 140 1114 147 204 156 291 1170 296 142 1140 164 1488 1448 1683 1105 154 648 654 1142 1681 166 1050 0\n1685 -26 144 -18 -10 -83 -140 111 37 43 0 140 1114 147 204 156 291 1170 296 1488 1448 648 1681 100 1050 0\n1686 -143 95 46 144 28 -18 0 419 626 1195 107 404 0\n1687 -140 -12 67 43 91 0 142 1109 1139 163 1682 1140 164 1117 162 1678 1488 1448 1680 119 291 1000 1001 1651 1181 1210 303 140 1220 908 907 1114 848 1648 150 1104 850 147 204 156 1684 122 410 607 1199 1103 420 418 1191 443 397 1685 505 284 963 657 1164 384 356 302 295 1686 86 639 1004 148 630 1141 1447 165 0\n1688 -45 117 -133 26 -18 194 34 0 68 171 639 260 1004 148 0\n1689 -77 120 102 71 -141 22 0 286 552 1150 6 266 0\n1690 -70 -133 28 -75 144 -18 -42 -12 23 43 91 0 410 1199 1448 1678 1488 607 1103 418 482 392 614 657 284 1175 296 871 147 1120 151 1028 68 997 168 1119 143 142 1109 1139 163 1682 1140 164 581 1102 270 1211 718 571 1153 1163 1106 1374 275 282 602 1033 1240 54 1101 417 1351 479 387 527 388 1192 400 454 404 1689 107 1036 155 591 192 35 141 0\n1691 -94 109 62 46 145 28 -75 144 -18 34 -42 111 -12 23 0 284 1175 296 68 997 147 168 1143 173 1119 143 142 1140 164 963 909 1181 302 664 291 1180 1106 1374 285 602 1033 99 54 155 591 192 141 187 140 1102 270 571 1163 35 282 0\n1692 -21 -142 0 150 583 1114 1210 140 0\n1693 -133 28 -75 144 -18 -42 -12 23 43 91 0 284 1175 296 96 1028 68 997 147 168 1119 143 1143 142 1109 1139 163 1682 1140 164 1678 1488 1448 131 410 607 657 1199 1103 418 614 1191 482 399 443 392 397 1688 1690 1691 1692 86 1686 302 664 1180 285 342 291 1106 1374 602 1033 99 54 155 591 192 141 187 140 1102 270 571 1163 35 282 0\n1694 28 -75 144 -18 -12 67 43 91 0 284 1164 618 96 147 1135 159 68 1687 513 168 1143 173 1119 143 1028 142 1109 1139 163 1682 1140 164 1117 162 1645 1678 1488 1448 1693 1353 291 1001 1651 1181 356 1210 303 295 140 908 907 122 1114 189 292 606 150 149 1103 1232 300 925 1161 1178 644 333 273 278 952 1004 921 0\n1695 -75 144 -18 -12 67 43 91 0 147 1645 1678 1488 1448 871 1694 156 1115 141 187 140 1102 270 718 571 1163 1353 282 410 607 1199 1103 418 597 482 35 392 0\n1696 75 -18 -12 67 43 91 0 1687 513 1028 68 997 865 168 1143 173 1119 888 142 1109 1139 163 1682 1105 154 690 262 1210 1220 1648 849 1268 1001 1679 929 1525 0\n1697 -18 -12 67 43 91 0 1687 513 168 1143 173 1119 143 1028 142 1109 1139 163 1682 1140 164 1117 162 1678 1488 1448 68 147 1135 159 1696 96 284 618 1695 1164 109 114 116 117 1423 1353 291 1001 1651 1181 356 1210 303 295 140 908 907 122 1114 189 292 606 150 149 1103 1232 300 925 1161 1178 644 333 273 278 952 1004 921 0\n1698 -12 67 91 43 0 1687 513 1028 1697 501 848 977 715 1220 870 1102 1651 714 1106 0\n1699 167 38 37 28 69 77 62 111 110 121 46 -18 259 39 88 26 137 124 144 -42 219 12 23 0 147 168 1119 143 149 203 155 950 948 1036 76 107 398 404 1190 434 412 392 54 1244 294 1173 0\n1700 -86 36 22 110 121 102 104 39 88 55 26 137 124 6 219 12 23 0 505 284 1175 294 1173 345 1244 285 1403 593 99 0\n1701 -27 109 -135 121 160 72 23 0 155 591 192 35 141 0\n1702 38 37 28 -240 62 111 110 46 102 104 -18 259 39 88 55 26 124 284 144 -42 -59 12 23 0 270 1178 315 279 1163 348 286 147 1120 151 571 414 168 1119 143 1113 138 282 1699 1124 163 1700 54 412 1190 469 398 392 1701 579 948 950 76 0\n1703 37 28 -240 62 111 110 46 102 104 -18 259 55 26 -132 144 -42 -59 12 23 0 147 1135 159 270 1163 723 872 505 284 340 288 1164 289 618 1033 1032 409 1198 168 1119 143 1702 633 1083 1355 1356 397 1087 1189 54 460 412 0\n1704 -37 69 79 80 110 129 -18 -132 -59 12 0 147 1135 159 1121 723 872 1033 1032 409 1198 414 164 580 603 1125 221 149 155 950 948 76 633 1355 1356 41 0\n1705 -93 62 111 110 46 102 -18 26 -141 -132 144 -42 -59 12 23 0 147 1120 151 270 1163 723 872 505 284 340 288 1164 289 571 618 417 1205 390 1188 568 282 300 1178 348 315 286 279 1704 1703 108 156 554 599 1354 1111 35 136 271 1212 6 1154 281 0\n1706 -135 38 45 109 119 21 46 102 -18 39 88 137 -141 144 -42 -59 23 0 147 1120 151 571 417 1205 568 168 1113 138 1119 270 1163 282 1153 275 1211 412 579 1701 1190 950 948 1036 398 76 915 644 86 1351 387 527 969 1192 411 400 451 1689 403 1364 99 546 0\n1707 62 111 -18 26 -141 -132 34 -42 -133 -59 12 23 44 112 63 0 147 1135 159 1120 151 270 1163 723 872 505 284 340 288 1164 289 1121 410 417 1188 437 393 571 657 618 1199 479 388 1205 1033 1032 568 409 1198 414 168 1119 143 1113 138 1143 420 282 1153 275 1211 1705 1103 418 1692 1191 482 399 443 392 397 1244 1688 1083 1173 294 1706 54 164 603 1704 221 1225 78 82 84 644 155 35 915 86 1036 1212 592 1351 99 527 969 546 1689 1364 0\n1708 -62 -42 44 112 63 0 273 614 1178 1103 300 0\n1709 62 -18 63 26 -141 -132 34 -42 -133 -59 12 23 44 112 0 1707 394 616 1206 1103 418 0\n1710 -59 67 43 91 0 1698 1645 1678 1488 1448 1651 1353 1315 513 1028 1106 884 1240 759 1101 1647 763 1104 1708 1709 0\n1711 110 111 135 79 19 -132 13 80 129 62 30 31 -10 12 0 1018 1260 1087 603 54 0\n1712 -132 -42 26 62 67 43 91 0 1710 1210 140 1114 1220 848 1104 147 204 168 223 155 1119 143 1113 138 1143 1028 1648 850 505 284 1175 296 1164 289 618 1108 1135 227 157 229 158 156 159 150 1448 1678 1488 907 908 1698 121 409 1033 1353 1374 410 657 1037 1036 1183 909 1686 389 86 1688 71 397 574 1263 1018 1189 991 460 464 1062 412 418 1103 616 1711 393 1186 463 417 1101 299 1417 563 1177 1461 0\n1713 -117 61 111 87 -83 20 13 80 129 62 30 31 -10 12 0 71 397 635 1260 1202 605 413 953 0\n1714 37 135 117 111 87 -83 20 13 34 26 62 -18 -10 0 291 1220 848 54 294 1160 332 278 1004 148 630 1141 953 165 0\n1715 -37 61 -83 80 129 30 31 -10 12 0 140 164 605 1140 1260 188 148 0\n1716 61 111 87 -83 20 13 34 80 129 26 62 -18 -10 12 0 140 147 1135 229 158 159 1713 1715 1714 412 1201 393 1260 148 630 1141 953 165 0\n1717 -19 35 95 94 96 145 194 -75 28 -18 21 70 119 0 173 148 960 260 86 171 0\n1718 133 35 225 78 127 96 145 47 176 43 0 122 292 1413 359 1101 299 0\n1719 -61 243 145 194 34 -75 26 30 28 176 -18 21 70 119 12 44 43 0 284 384 302 173 963 303 1488 1448 49 50 51 272 1214 987 1155 379 300 1103 418 1408 1191 1718 410 657 1199 443 420 1686 397 86 1688 0\n1720 -42 26 62 67 43 91 0 1710 1210 1220 1648 850 505 284 1164 289 848 1104 618 140 147 1135 229 158 1114 204 156 1108 227 150 1448 1678 1488 907 908 1698 168 1028 1119 1143 211 143 149 1712 509 291 1001 1181 356 295 1719 1716 394 616 1206 1103 418 0\n1721 61 -289 145 47 -83 -140 -75 -18 -10 12 43 0 416 1204 483 393 1206 394 284 291 1181 384 302 1164 356 295 303 289 618 140 147 1135 229 158 1114 204 156 159 1488 1448 1715 1260 148 630 1141 208 165 162 1447 960 0\n1722 -142 145 47 -83 -140 -75 -18 -10 12 43 0 284 291 1181 384 302 303 140 1108 147 1135 227 157 229 158 1114 204 156 418 1721 49 51 272 1214 608 987 1155 1426 1718 1101 410 299 563 1183 376 389 267 1598 0\n1723 -257 35 26 62 67 43 91 0 1698 1710 1210 1220 848 1104 147 1135 159 140 229 158 1648 850 505 618 284 1164 289 1720 1107 1680 291 1181 1448 1678 1488 1000 1001 1722 1103 300 379 272 1715 982 384 302 356 295 303 119 416 1184 1114 1441 1108 227 157 204 156 907 908 1186 1201 1527 412 1398 1682 1716 54 77 79 294 1447 1070 1160 960 1202 332 397 278 1004 0\n1724 35 26 62 67 43 91 0 1698 1710 1210 1220 848 1104 147 1135 159 140 229 158 1648 850 505 618 284 1164 289 1720 1107 1680 291 1181 1448 1678 1488 1000 1001 1722 1103 300 379 272 1715 384 302 356 295 303 1114 1441 204 156 150 1108 907 908 1723 393 1260 148 630 960 1141 86 165 241 1052 163 1682 0\n1725 26 62 67 43 91 0 1710 1210 140 1220 848 1104 147 1135 229 158 159 1648 850 1114 1698 1678 1488 1448 505 284 618 1164 289 1720 1107 1680 291 1000 1001 1181 1722 1103 300 379 272 1724 162 610 208 1260 148 0\n1726 -144 96 145 47 35 -26 28 0 114 1384 0\n1727 62 67 43 91 0 1710 1210 140 1114 1220 848 1104 147 204 156 1108 179 187 1648 1725 154 849 1142 219 1268 166 247 245 242 162 291 1000 1001 648 165 164 163 1170 1181 1682 296 303 1726 1685 513 168 1119 211 223 143 149 155 950 948 953 0\n1728 67 43 91 0 1678 1488 1448 1698 1710 1210 140 1220 1114 848 1648 1104 850 147 204 156 1727 58 62 273 1708 1178 1107 300 1680 1103 291 1000 1001 1722 1181 1105 303 154 1685 219 1726 162 0\n1729 -35 -83 43 91 0 1728 983 1210 140 1128 1537 1410 1105 154 216 158 1108 1127 215 157 1449 1265 1114 277 1169 289 1678 124 162 1020 1112 1117 208 137 142 148 1018 1601 1600 565 1200 1101 417 942 473 1107 416 0\n1730 -54 19 12 -140 -83 -67 44 43 0 416 983 1210 140 1128 1537 1410 1105 154 216 158 1142 166 648 277 1169 291 356 295 1170 296 1449 1265 1181 1114 150 1448 1488 907 908 289 1020 1527 410 1186 1196 393 388 1260 272 379 300 1103 418 1191 445 443 398 397 1473 69 1590 639 1023 86 403 419 453 1195 0\n1731 -133 19 12 -140 -83 -67 44 43 0 1730 416 983 1210 140 1128 1537 1410 1105 154 216 158 1108 1127 215 157 1142 166 648 277 1169 291 356 295 1170 296 1449 1265 1181 1114 150 1448 1488 907 908 289 410 1183 1199 389 1601 563 1101 417 1188 479 437 388 393 1260 272 379 300 1103 418 1191 445 443 398 397 1473 69 1590 639 1023 86 403 419 453 1195 0\n1732 -61 133 128 12 35 30 176 96 145 47 43 0 49 272 1214 987 1155 1718 0\n1733 19 12 -140 -83 43 91 0 416 1204 1184 1729 1728 983 1210 140 1128 1537 1410 1105 154 216 158 1108 1127 215 157 1142 166 648 277 1169 291 356 295 1181 303 1170 296 1449 1265 1001 1000 119 1114 150 1448 1678 1488 907 908 289 1158 1018 1730 1731 122 292 654 361 301 1487 1038 1732 1715 1260 1398 393 1682 483 418 1103 300 1178 348 273 286 1069 403 625 1194 1070 0\n1734 -19 -140 -83 43 91 0 416 1729 1728 1537 983 1210 1410 1105 154 1142 166 648 277 1169 291 356 295 1181 303 1170 296 1001 1000 140 1108 1678 1488 1448 148 630 1141 165 244 241 164 163 1682 1447 93 419 636 1195 122 453 410 403 1199 1511 1023 1101 1590 417 388 479 0\n1735 -140 -83 43 91 0 1729 1728 1537 983 1210 1410 1105 154 1142 166 648 277 1169 291 356 295 1181 303 1170 296 1449 1265 1001 1000 140 1128 152 1114 150 1448 1678 1488 907 908 570 289 1158 282 416 1204 1734 1733 1235 122 410 607 1199 1103 420 418 1409 1191 1081 445 443 398 397 1473 69 1038 639 86 419 1195 453 403 1511 1069 1101 595 1024 35 0\n1736 -83 43 91 0 1728 983 1210 140 1128 152 1114 150 1448 1678 1488 907 908 570 277 1169 1158 291 1410 1537 1000 1001 1170 1181 356 1105 296 303 295 154 648 1142 166 1729 1735 513 168 942 1514 1143 252 1101 1487 1038 172 299 926 1157 70 923 941 122 1582 0\n1737 -19 -42 43 91 0 1736 1028 1106 409 1198 414 1728 1009 1033 1032 983 1210 140 1114 168 211 149 1119 143 1143 1448 1488 1678 1708 1353 410 1199 1557 150 1108 907 908 148 631 637 1584 1141 260 1487 505 244 241 171 657 1492 164 163 86 1101 1682 644 299 952 935 1157 1036 1223 0\n1738 -75 -42 43 91 0 1736 1028 1106 409 1198 414 1728 1009 1033 1032 983 1210 140 1114 168 211 149 1119 143 1448 1488 1678 1708 1353 410 1199 1108 1127 1128 277 284 657 1175 367 295 1514 1487 1492 1101 299 1157 1223 1036 155 624 1130 221 220 165 164 163 953 1682 0\n1739 -42 43 91 0 1736 1353 410 1183 389 1728 1557 277 1169 289 983 1210 1678 1488 1448 168 1028 1708 1113 1119 1106 138 143 409 1009 1032 1033 1198 414 1737 1738 1265 1449 1105 1463 1312 1018 1646 252 157 158 172 1590 1514 295 1174 278 69 397 574 1189 460 464 412 418 1103 616 607 987 991 1711 1062 393 1186 463 417 1101 299 1417 563 1177 1461 0\n1740 19 -87 -26 -140 -133 83 -67 44 43 0 295 1174 278 983 1210 140 1128 154 216 158 1108 1127 215 157 96 1449 620 410 1183 389 277 1169 289 1488 1448 981 1018 69 1106 397 574 1189 464 418 1103 607 987 991 1091 0\n1741 -87 -26 -140 -133 83 -67 44 43 0 1557 1740 631 1584 509 1148 161 0\n1742 -19 -26 43 91 0 1728 620 154 1739 1107 1736 1353 1557 983 1210 140 1108 1488 148 637 1584 1141 1487 1148 1271 241 161 1101 163 1106 1278 0\n1743 94 6 -92 137 88 87 -26 -140 -133 83 -67 44 112 0 299 1177 268 96 1463 166 410 1199 1557 1590 1511 663 1474 1446 0\n1744 -132 -26 43 91 0 1742 1678 1728 1736 1353 1739 1107 1741 983 1210 140 1128 154 216 158 1108 1127 215 157 96 1463 166 1449 620 97 416 410 1183 389 1488 1448 409 884 1032 1198 758 414 762 1101 1416 563 1743 93 1473 81 85 398 1440 1190 1513 474 1682 418 559 1103 1601 607 0\n1745 -26 43 91 0 1739 1107 1736 1353 1728 1557 983 1210 140 1108 1127 1128 277 1169 289 1678 1488 1448 96 154 620 1449 1129 215 216 1741 1742 1744 509 161 955 1148 234 232 233 262 165 163 164 172 1682 1590 1447 93 0\n1746 -37 -94 -140 83 -67 0 277 301 1179 328 285 983 1210 1442 1446 0\n1747 -75 118 87 -94 39 -140 83 -67 0 284 1374 1175 1473 296 0\n1748 118 87 -94 -34 26 -140 83 -67 0 301 1179 643 161 1136 166 1747 1105 402 652 1203 1369 414 0\n1749 -111 76 -34 43 91 0 161 1136 166 1745 1739 1107 416 1728 1736 1557 983 1210 140 1108 1127 394 1682 1187 163 1443 473 220 232 985 417 155 1101 1298 1105 402 652 1203 99 414 0\n1750 -94 -34 43 91 0 1745 1739 1107 1736 1353 1728 983 1210 277 1488 1448 93 301 637 1179 1092 328 285 1746 1748 81 1749 85 1447 0\n1751 -34 43 91 0 1745 1739 1107 416 1184 390 1736 1353 410 1199 1728 1557 983 1210 140 1114 150 1448 1678 1488 907 908 161 1136 1148 166 1750 1487 1486 1105 402 979 652 1193 1203 299 1416 465 414 1177 419 1511 268 86 105 1443 951 171 1749 260 1512 148 1092 0\n1752 43 91 0 1728 1736 1739 1107 1745 1751 1106 1320 1311 0\n1753 -43 0 898 1250 1414 1406 808 0\n1754 -63 0 1753 1448 0\n1755 -112 0 1753 1488 0\n1756 91 0 1753 1752 0\n1757 -140 0 1756 133 0\n1758 238 0 1756 298 0\n1759 481 0 1756 893 0\n1760 -202 0 1758 1152 0\n1761 -243 0 1758 1176 0\n1762 -55 0 1760 268 0\n1763 -96 0 1761 303 0\n1764 -27 36 76 111 -83 -67 0 1758 1762 1753 1756 1754 1755 983 1210 883 754 756 1101 566 417 1205 390 951 1410 1537 505 648 291 1170 296 154 1142 166 1011 1615 277 1169 356 372 301 957 1487 295 358 140 1128 1158 155 624 1130 221 165 164 953 57 612 1496 1103 1562 300 286 348 0\n1765 102 36 76 111 -83 -67 0 1758 1753 1762 1756 1755 983 1210 1410 1537 505 154 1142 166 648 291 1170 296 1764 99 403 1194 413 625 883 754 756 1101 566 417 1205 390 951 1011 1615 277 1169 356 372 301 957 1487 295 358 140 1108 1127 151 1403 1566 953 57 1496 1562 1395 0\n1766 36 76 111 -83 -67 0 1756 1753 983 1210 883 754 756 1101 417 1205 1410 1537 505 154 1142 166 648 291 1170 296 1764 99 403 426 1765 388 0\n1767 -36 -83 -67 0 1760 1756 1753 983 1210 883 754 756 1101 417 1205 140 1128 1410 1537 505 154 216 158 1108 1127 215 157 291 310 267 1449 1265 119 277 1169 289 163 561 1398 1139 43 49 137 51 1598 0\n1768 -110 111 -83 -67 0 1762 1753 1758 1756 1754 1755 277 1158 1767 1766 285 345 371 300 101 983 1210 883 754 756 1101 566 417 1205 390 951 1410 1537 505 154 1142 166 1169 291 356 372 301 957 648 1497 1021 1145 612 170 1103 0\n1769 -19 111 -83 -67 0 1758 1762 1753 1756 1757 983 1210 883 754 756 1101 566 417 1205 390 1767 951 1410 1537 505 154 1142 166 277 1169 291 356 372 301 957 648 1659 1507 57 0\n1770 12 111 -83 -67 0 1760 1756 1753 1762 983 1210 277 1169 289 1410 1265 1449 1769 1018 1768 1767 883 754 756 1101 417 1205 390 140 1128 1537 505 154 216 158 1108 1127 215 157 566 291 310 267 1260 49 272 1155 1412 354 1598 293 556 22 0\n1771 111 -83 -67 0 1753 1758 1762 1756 1754 1755 1767 983 1210 883 754 756 1101 417 1205 390 1410 1537 505 154 1142 166 291 1170 296 277 1169 356 295 648 372 301 957 1501 566 1158 1766 285 345 371 300 1770 142 601 1140 975 164 612 1496 1103 0\n1772 -83 -67 0 1753 1756 1762 983 1210 883 754 756 1101 417 566 1205 390 1767 1771 949 0\n1773 -36 76 -67 0 1756 1772 1382 1463 166 1633 509 161 1557 983 1210 140 1108 1127 163 1443 1138 220 233 155 980 1105 402 652 1203 99 414 0\n1774 133 126 -92 -67 0 1761 1759 1756 1755 1772 1557 1382 1265 1449 983 1210 787 894 791 505 154 299 376 267 1633 509 980 158 1576 277 1169 1381 1546 292 1487 361 301 0\n1775 -133 -111 -67 0 1761 1758 1753 1759 1756 983 1210 140 1108 1127 1772 1382 394 1187 411 1217 277 1158 1632 300 348 347 285 1773 1411 1101 787 894 791 505 154 215 157 1633 509 980 158 299 376 267 161 1148 1449 1265 1557 410 563 1183 1584 389 607 1601 0\n1776 -111 -67 0 1754 1755 1758 1753 1759 1761 1756 1772 1382 1449 1265 1633 509 1557 983 1210 140 1114 150 277 1169 1158 394 1217 617 1632 1187 908 907 300 411 348 347 285 1773 1411 1101 299 787 376 894 267 791 505 154 980 158 1576 1775 1381 1774 292 1038 361 301 0\n1777 133 70 119 35 -92 -67 0 1756 1772 983 1210 140 1114 150 277 1169 1381 1774 292 1038 361 301 0\n1778 -92 -26 -67 0 1756 1763 1761 1754 1755 1633 1772 509 161 1148 154 262 172 983 1210 140 1108 1127 215 157 980 158 173 666 1382 1449 1265 1557 277 1169 289 299 376 267 1576 1230 908 907 1777 410 1590 1584 563 1183 301 389 382 1601 278 607 69 1103 397 418 443 1191 0\n1779 -26 -67 0 1753 1757 1756 1762 1776 1633 1772 509 161 1148 983 1210 140 1108 1127 154 215 232 163 1778 1101 417 566 1581 1525 1188 1205 1579 390 1477 0\n1780 -36 -67 0 1756 1760 1772 1382 1463 1557 163 1773 985 285 266 308 0\n1781 -125 -67 0 1757 1762 1759 1753 1756 1772 983 1210 1382 1779 1105 791 894 787 1101 566 417 1205 1188 390 1606 1780 1411 411 1187 1525 1449 277 1169 289 1633 509 1265 161 1148 402 1193 1572 955 1092 1776 173 666 1463 403 625 433 392 1566 1573 957 1575 1567 48 0\n1782 -256 -67 0 1759 1753 1762 1756 983 1210 1772 1382 1779 1105 791 894 787 1101 417 1205 390 1633 509 566 1780 1362 1477 1188 1557 1019 402 1185 432 448 437 405 410 1553 1560 11 0\n1783 -84 -12 -67 0 1759 1753 1756 983 1210 1772 1382 1779 1105 791 894 787 1101 417 1188 1633 509 161 1148 140 1128 152 570 277 1158 282 974 300 1359 348 0\n1784 -127 5 -67 0 1762 1759 1753 1754 1755 1756 1761 1782 392 983 1210 1772 1382 1779 1105 791 894 787 1101 417 1205 390 566 1633 509 1780 1477 277 1169 289 1265 1449 161 1148 402 1193 1572 1018 1188 1557 1019 140 1114 150 405 1214 1186 393 1493 1451 42 1117 257 162 170 908 907 1783 1381 410 1563 1592 465 69 419 639 86 0\n1785 -78 -67 0 1757 1759 1753 1756 1762 1782 392 983 1210 1772 1382 1779 1105 791 894 787 1101 417 1205 390 1633 509 566 1780 1362 1477 1525 1188 1606 1449 277 1169 289 1265 161 1148 402 1193 1572 955 1092 1203 414 652 1776 1463 166 1557 287 1215 1560 1564 1167 77 80 81 266 1545 1472 0\n1786 5 -67 0 1756 1759 1753 1762 1785 983 1210 1772 1382 1779 1105 791 894 787 1101 417 1205 390 1633 509 566 1780 1362 1477 1557 1019 1784 11 0\n1787 -76 -67 0 1759 1753 1756 1762 1760 1772 983 1210 1382 1779 1105 791 894 787 1101 566 417 1205 1188 390 1606 1557 285 1472 308 266 0\n1788 -280 -67 0 1757 1759 1753 1756 1772 983 1210 1382 1779 1105 791 894 787 1101 417 1188 1780 1525 1449 277 1169 289 1633 509 1265 161 1148 402 1193 1572 955 140 1128 1203 414 1463 166 652 1781 1787 99 155 221 164 1776 1130 165 1573 1782 392 437 465 393 419 1568 0\n1789 -67 0 1756 1759 1753 983 1210 1772 1382 1779 1105 791 894 787 1101 1786 1788 1553 410 0\n1790 -23 0 1789 1645 0\n1791 -119 93 -59 0 1754 1755 399 584 1191 1103 418 0\n1792 -69 -134 101 64 113 0 1760 279 533 305 1100 265 0\n1793 -223 69 94 136 -124 -280 0 1759 1753 1789 1758 1756 850 1648 1220 1102 1211 270 1153 275 788 1101 402 1193 465 417 478 387 1352 463 97 977 1104 997 161 147 1135 234 165 1163 1165 345 295 371 300 1791 1363 171 647 1146 149 76 0\n1794 -93 79 31 -59 80 129 110 -133 0 1761 270 300 607 379 272 314 278 1355 1356 41 0\n1795 -69 101 -141 211 185 113 0 1760 1756 275 279 1792 305 334 265 293 1100 1411 135 163 241 0\n1796 231 133 -5 29 0 1753 1756 137 1112 162 15 14 13 292 1025 1381 0\n1797 83 132 -26 77 95 126 133 35 28 0 1756 154 509 1381 161 654 1148 107 262 172 0\n1798 -26 -94 95 -18 -297 126 133 35 28 0 1758 1756 301 1166 347 285 286 154 849 1142 852 166 1797 291 648 1170 296 1615 1011 909 0\n1799 -94 -231 -18 -297 126 133 35 28 0 1171 302 850 301 1166 343 1798 284 1105 0\n1800 83 132 -19 70 94 119 133 35 21 0 1756 148 509 1381 161 636 1148 86 260 171 0\n1801 -143 88 137 136 39 38 69 95 -18 126 28 0 1756 419 626 642 1207 398 76 950 101 660 1615 107 0\n1802 -26 -19 69 70 94 95 -18 -297 126 119 133 35 28 21 0 1756 148 1141 165 147 154 849 1142 852 166 1800 291 630 648 1170 296 1801 86 171 647 1146 149 203 76 155 950 0\n1803 -19 -13 94 95 126 119 133 -92 35 28 21 0 1789 1759 1755 1754 1758 1756 612 143 1145 170 1103 300 1161 336 279 788 1210 907 1220 848 1104 147 1648 850 148 1141 165 1802 1105 284 871 720 1175 719 296 717 1381 1800 1374 636 1033 631 86 171 647 1146 149 203 76 155 948 0\n1804 -143 69 88 137 186 95 -18 126 28 0 1756 147 247 165 166 626 1801 622 1615 1011 107 0\n1805 44 70 143 137 83 88 227 129 -12 94 124 -18 119 133 35 21 0 1756 1755 1754 1758 147 86 171 1146 203 155 149 1381 641 647 606 289 1135 159 1103 925 300 1800 1161 1033 631 1083 336 948 76 279 0\n1806 -13 117 44 -75 -231 126 119 133 -92 35 28 21 0 1759 1789 1756 1754 1755 284 1164 289 788 1210 1220 848 1104 618 1648 1799 1171 302 147 1135 159 612 1803 1103 69 300 278 360 1159 0\n1807 132 13 20 118 70 83 -75 94 62 -10 119 133 35 21 0 1789 1753 1756 1758 284 1164 289 1220 848 1104 618 147 1135 159 509 1800 161 1361 955 981 279 1029 1160 1632 371 300 0\n1808 -143 44 186 137 88 95 62 -10 126 28 0 1789 1758 1753 1754 1755 1756 140 1220 848 1104 147 187 245 164 247 165 642 1804 82 84 279 1160 371 300 1632 1103 953 612 0\n1809 44 186 137 88 94 95 62 -10 126 119 28 21 0 1789 1758 1753 1754 1755 1756 140 1220 848 1104 147 187 245 164 247 165 166 907 1808 86 171 647 1146 149 203 155 950 948 76 279 1160 371 300 1632 1103 953 612 0\n1810 -26 -83 94 95 62 -10 126 119 28 21 0 1789 1756 291 1170 296 140 1220 848 1104 147 187 154 648 1142 166 247 245 165 164 1809 170 617 1145 143 189 192 149 155 950 948 953 0\n1811 -83 94 95 126 119 -92 28 21 0 1758 1759 1789 1756 788 1210 1220 1648 850 848 1104 299 1157 324 273 1810 1105 871 720 717 719 0\n1812 -26 83 94 95 -10 126 119 133 35 28 21 0 1789 1754 1755 140 1220 848 1104 147 187 1648 154 849 202 191 852 509 1797 161 626 1148 260 257 171 170 86 907 0\n1813 -143 -132 34 44 227 129 -84 -231 119 -92 21 0 1789 1759 1757 1754 1755 409 1209 289 299 1157 322 272 788 1210 140 1220 848 1104 147 1135 229 158 159 419 636 485 1235 1260 397 393 1007 483 1159 418 360 1103 300 0\n1814 44 -231 126 119 133 -92 35 28 21 0 1759 1789 1758 1753 1756 1754 1755 788 1210 1220 1648 850 1171 302 848 1104 1799 1811 1812 1105 284 1175 296 1164 289 1374 618 1381 299 1157 322 272 140 147 1135 229 158 159 324 273 907 1809 1136 161 1106 409 1033 1209 1813 1805 86 171 647 641 1146 1806 1083 149 203 155 950 948 76 279 1160 371 300 1632 1103 953 418 164 483 1140 393 188 1260 148 0\n1815 159 -44 80 129 145 47 -92 54 29 0 1789 1759 1763 788 1210 140 1220 848 1104 147 1135 229 159 142 188 918 148 0\n1816 -10 75 83 -141 0 1789 1756 1220 848 1648 1104 850 962 505 1106 849 852 0\n1817 95 -133 83 126 77 -141 28 -3 0 1789 1756 1758 410 1199 420 5 4 1423 107 1463 172 166 1147 155 1816 1102 270 973 1153 509 709 869 977 1105 1104 402 652 147 1203 247 414 1795 948 1615 285 1165 1793 372 301 0\n1818 68 12 61 79 129 31 -59 80 110 0 1355 1356 41 0\n1819 -68 119 143 -133 70 21 0 1761 278 639 382 86 301 0\n1820 -44 30 128 79 194 -133 259 0 170 943 257 142 0\n1821 83 126 84 77 -141 35 28 -3 0 1761 1789 1756 1754 1755 417 1188 537 135 1110 150 1381 410 437 393 1817 302 655 384 977 284 1104 1816 1105 147 997 619 1102 402 1135 161 877 1193 159 1148 743 407 465 970 1794 419 1791 1819 1355 1356 1820 1103 418 1191 443 397 69 148 637 260 86 171 0\n1822 -133 -83 126 111 62 77 -141 28 21 0 1789 1758 1756 1754 1755 883 755 1210 140 1220 848 1104 147 187 1648 850 291 1170 373 302 296 1423 1105 154 927 648 1142 172 166 247 245 1147 1615 165 164 155 285 622 950 1165 372 301 957 1810 953 908 143 170 1145 0\n1823 13 26 20 61 118 -83 111 104 62 6 0 1756 1789 1762 291 883 755 1210 1220 1648 850 505 284 1164 356 295 289 848 1104 618 119 1716 142 601 1140 975 164 294 1714 1160 921 279 0\n1824 26 20 61 118 -83 111 104 62 6 0 1789 1756 1754 1755 1758 883 755 1210 1220 848 1104 147 1135 159 1648 850 291 358 505 284 618 1164 289 356 295 1823 143 612 1145 170 1103 300 1161 336 333 279 278 921 69 148 630 1141 76 165 0\n1825 -45 69 -34 26 -18 0 1756 147 1135 161 234 165 1148 159 171 647 1146 260 149 148 1361 1105 402 619 1193 407 981 955 76 0\n1826 -59 -18 -133 83 109 -126 -141 -3 0 1756 1761 1790 147 1135 159 627 865 417 1188 410 437 393 404 1195 419 537 135 1110 150 5 4 270 973 571 690 1153 1163 509 282 161 877 234 743 1795 970 1825 86 1791 300 607 596 379 35 272 314 1244 587 41 278 402 619 1355 1193 407 0\n1827 -44 135 86 128 79 30 -133 111 104 259 6 0 1762 170 943 1145 142 143 975 0\n1828 -117 80 -132 30 129 -10 31 -133 111 -141 0 1756 1754 1755 1761 409 417 1188 410 437 393 1205 390 566 71 397 574 1018 1189 1087 460 464 412 418 1827 972 1103 1260 300 272 379 0\n1829 160 117 -134 39 88 80 -132 137 129 20 -10 -18 111 104 62 6 0 1762 147 1135 159 1083 140 229 158 187 143 192 155 950 948 1054 953 69 164 148 244 1141 0\n1830 160 37 38 39 137 20 -10 88 111 62 0 1789 140 1220 848 1104 147 187 143 192 155 950 948 953 0\n1831 160 117 20 103 -132 137 127 -75 -141 -10 -18 5 29 0 1789 1756 1762 284 1164 289 618 147 1135 159 1083 417 1205 1220 1648 850 962 1435 566 390 949 951 1033 1032 1829 1830 1411 1436 1062 18 0\n1832 -133 143 94 103 -132 137 127 -75 70 -141 -10 -18 5 29 21 0 1789 1762 1756 1754 1755 1758 957 284 1164 289 417 1205 1220 1648 850 962 1435 566 390 949 951 1033 1032 618 147 1135 140 229 158 159 1828 1083 1831 1145 170 908 86 1819 171 647 69 1146 148 631 203 1141 155 244 948 164 76 953 279 612 1160 1103 371 300 0\n1833 -26 174 -297 83 0 154 849 218 852 161 509 0\n1834 -44 133 -92 -10 -18 83 29 0 1789 1761 1758 1756 1763 299 1157 324 273 376 267 1220 1648 850 147 1135 140 229 158 187 159 170 617 1145 237 143 189 192 162 149 1833 1381 505 125 129 284 618 1374 1164 1175 289 296 1815 1140 195 164 161 1106 409 1033 1830 1083 397 917 1189 602 460 54 412 0\n1835 35 44 133 126 119 -92 83 28 21 0 1756 1381 1814 292 0\n1836 -126 119 45 70 -18 28 21 0 111 115 117 627 1686 86 0\n1837 -75 12 54 103 219 26 121 5 -4 0 1790 136 1133 157 98 540 1257 11 0\n1838 -61 -141 -83 5 29 0 1760 1789 1756 883 755 1210 140 1220 848 1104 147 1135 229 158 291 310 267 43 49 51 272 1598 1155 1412 0\n1839 26 61 70 -141 -83 29 21 0 1758 1760 1789 1757 1756 1754 1755 1762 417 1205 390 566 883 755 1210 140 1220 848 1104 147 1135 229 158 159 1648 850 291 310 267 358 119 505 284 618 1164 289 356 361 295 301 957 1398 1525 949 1824 398 578 647 1190 1207 412 419 86 908 170 1145 143 1716 975 142 0\n1840 160 111 62 37 38 39 137 -83 0 1756 883 755 1210 140 291 1170 296 189 1830 149 0\n1841 94 44 111 62 186 137 70 -141 95 -10 88 28 21 0 1789 1756 1754 1755 1758 908 140 1220 848 1104 147 187 245 164 247 165 166 957 1809 1836 171 647 1146 203 155 950 948 76 953 279 612 1160 1103 371 300 0\n1842 5 117 -44 20 103 -132 137 -75 -141 29 -10 0 1756 1789 1757 1762 284 1164 289 1220 848 1104 618 147 1135 159 1083 170 1145 617 1648 850 1033 1032 417 1205 390 962 566 1435 1831 1525 20 1830 1436 0\n1843 -133 -44 20 103 -132 137 -75 -141 29 -10 0 1789 1756 1757 170 1145 617 284 1164 289 1220 1648 850 1033 1032 417 1205 390 848 1104 618 962 566 140 147 1135 229 158 159 1828 609 1842 12 557 1398 1411 1525 1829 0\n1844 -44 20 103 -141 29 -10 83 0 1789 1756 1762 1816 284 1164 289 417 1205 390 1220 1648 850 848 1104 962 1106 1374 618 566 140 147 1135 229 158 159 170 617 1145 143 1843 1553 1555 1842 71 574 1018 1427 1597 142 0\n1845 -5 136 87 118 -133 20 80 -132 129 -141 -10 -3 0 1789 1756 1762 417 1205 390 1220 1648 850 848 1104 962 566 140 147 1135 229 158 135 227 157 159 5 4 3 12 13 15 557 1012 1411 949 1792 1828 76 1083 0\n1846 -133 44 103 -132 137 -75 -141 -10 -3 0 1789 1761 1757 1762 1756 1754 1755 1758 908 1220 848 1104 135 1110 147 204 156 1003 409 1209 421 963 957 284 384 302 1164 289 1648 850 1033 1032 417 1205 390 618 962 537 566 140 1135 229 158 227 157 159 150 410 657 1199 420 1686 86 171 647 1146 203 155 950 948 1845 1435 1832 1525 949 20 1828 1436 1083 953 76 612 279 1103 1160 300 371 0\n1847 -117 -141 -10 83 -3 0 1755 1754 1757 1761 1762 1789 1756 1816 1374 1220 1648 850 848 1104 962 1106 566 135 147 1135 227 417 1205 1552 157 1110 204 156 1003 409 1209 421 963 957 1844 1846 1555 1553 908 284 1164 289 1032 618 537 140 229 158 159 150 71 397 574 528 1018 485 1427 11 419 1805 1340 162 0\n1848 -45 38 37 111 62 44 20 39 88 137 -10 0 1789 1756 1754 1755 1758 1220 848 1104 147 171 647 1146 203 155 950 948 953 76 612 279 1103 1160 300 371 0\n1849 76 -143 95 39 88 137 28 -18 0 1756 1615 1011 1686 0\n1850 -141 -10 83 -3 0 1789 1761 1754 1755 1757 1762 1756 1763 140 1220 848 1104 147 1135 229 158 135 227 157 1110 204 156 159 1648 850 150 5 4 3 2 417 566 537 1816 962 1205 284 618 1374 1106 390 1552 1164 384 409 1003 1032 1033 289 302 1209 421 963 957 1844 908 1846 1553 1555 1435 1525 949 1436 1847 1083 1848 86 1849 101 622 950 954 148 1365 208 162 0\n1851 -44 -92 29 -10 83 0 1789 1761 1758 1756 1763 299 1157 324 273 376 267 140 1220 848 1104 147 1135 229 158 159 187 1648 850 170 617 1834 1145 124 126 131 143 189 192 149 1833 505 284 618 1374 1164 1175 289 296 1815 1140 195 164 161 1106 409 1033 1830 1083 397 917 1189 602 460 54 412 0\n1852 -117 5 -133 -75 44 54 29 -10 0 1789 1754 1755 410 1183 389 284 1164 289 1220 848 1104 618 140 147 1135 229 158 159 71 397 574 1018 1189 1427 464 607 418 1103 0\n1853 -133 -75 119 -92 29 28 -10 83 21 0 1755 1754 1789 1761 1753 1756 1758 284 384 302 1175 296 1164 289 1374 1220 848 1104 618 1851 907 299 1157 324 273 376 267 147 1135 159 140 126 131 410 563 657 963 1199 420 1686 86 1819 171 647 1146 149 203 155 1852 69 148 1141 188 1140 207 165 164 161 1106 651 631 948 1848 76 1632 279 300 336 1161 0\n1854 -5 34 -75 119 -92 29 28 -10 83 21 0 1757 1789 1761 1758 1753 1756 1754 1755 1220 848 1104 1106 1003 409 1209 421 963 1648 850 1033 1853 284 1175 296 1164 289 1374 618 1851 907 299 1157 324 273 376 267 140 147 1135 229 158 159 13 15 1796 1538 322 1814 1381 272 1836 1813 171 647 641 1805 1146 1083 149 203 155 950 948 76 279 1160 371 300 1632 1103 1848 418 164 483 1140 393 188 1260 148 0\n1855 -117 94 292 133 70 119 178 83 21 0 1756 397 485 419 86 171 641 238 1381 162 0\n1856 -35 5 -75 -92 29 -10 0 1761 1789 284 1164 289 1220 848 1104 618 299 376 267 140 147 1135 229 158 159 162 565 1273 1340 11 0\n1857 19 12 -231 117 -132 34 -75 44 -92 -10 0 1789 1757 1754 1755 299 1157 322 272 409 1209 284 1164 289 1220 848 1104 618 140 147 1135 229 158 159 1007 1260 1159 393 360 483 300 418 1103 0\n1858 34 -75 119 -92 29 28 -10 83 21 0 1755 1754 1789 1757 1761 1758 1753 1756 1853 284 1175 296 1164 289 1374 1220 848 1104 618 1851 907 299 1157 324 273 147 1135 159 1648 850 140 1106 409 1003 1033 1209 421 963 1854 1855 1083 1856 1381 1835 292 1836 1813 171 647 1805 1146 203 155 950 948 1857 149 76 148 279 1141 1160 244 371 164 300 1848 1632 0\n1859 -75 119 -92 29 28 -10 83 21 0 1789 1758 1755 1754 1761 1756 1851 907 299 1157 324 273 140 1220 848 1104 147 1135 229 96 284 1374 1175 384 296 302 1853 1858 120 161 666 1136 1148 234 233 166 173 165 164 963 1809 1836 171 647 1825 238 78 162 1848 1807 56 0\n1860 -10 83 -3 0 1789 1753 1754 1755 1756 1763 135 1110 150 1220 848 1648 1104 850 147 1135 204 227 156 157 1850 1101 538 1851 907 1859 1105 154 849 1833 219 852 1147 162 509 172 259 161 666 171 1148 1836 173 1835 928 1726 655 86 909 0\n1861 -75 119 45 69 28 -18 47 186 145 70 83 21 0 1761 1836 284 1374 963 1175 384 86 296 302 1804 0\n1862 -133 119 83 -3 0 1789 1759 1753 1756 1860 1102 788 1101 973 509 709 869 135 1110 150 537 666 161 1136 1148 173 977 1104 147 204 156 5 270 1153 4 247 1795 1825 1861 1105 402 1193 1836 417 3 124 128 410 1821 463 110 113 114 1363 909 0\n1863 -95 133 -124 83 0 1756 302 658 1171 1381 292 0\n1864 119 83 -3 0 1759 1753 1789 1758 1756 1860 1102 788 1101 973 509 709 869 977 1104 5 270 1153 4 161 1136 147 247 1795 1825 135 1110 204 156 1148 173 166 666 537 150 1836 1861 1105 402 652 1203 414 1862 1863 1804 86 301 1166 347 285 1615 1011 909 0\n1865 83 -3 0 1759 1753 1789 1756 135 1110 1860 1102 270 788 1163 1101 417 973 1188 509 709 869 977 1104 147 204 156 1864 1791 300 1360 348 124 128 286 1821 404 1826 434 392 0\n1866 -44 -133 -141 -3 0 1789 1756 1757 537 135 1865 883 755 1210 1220 848 1104 147 1135 227 157 140 187 179 1110 150 170 617 609 1145 1839 154 648 1142 166 247 242 245 165 163 164 1525 1840 0\n1867 -61 -141 -3 0 1760 1789 1756 417 1205 1865 883 755 1210 140 1220 848 1104 147 1135 229 158 135 227 157 291 310 267 119 43 49 51 272 1214 1838 987 1155 556 1012 354 1411 293 0\n1868 -133 -141 -3 0 1758 1757 1789 1756 1762 417 1205 390 566 135 1865 883 755 1210 1220 848 1104 147 179 1110 150 1135 227 157 537 1867 1839 154 1142 242 163 949 1525 648 204 156 291 1170 373 302 296 410 1199 420 1866 1841 627 909 1822 110 0\n1869 -141 -3 0 1758 1789 1756 1757 1762 135 1865 883 755 1210 1220 848 1104 147 1135 227 157 1110 204 156 140 187 179 1648 291 1170 373 302 296 150 417 566 537 1205 390 1867 1839 154 648 1142 219 166 247 242 245 165 163 164 1525 949 1840 1145 1868 162 170 1841 627 1798 0\n1870 -75 -3 0 1789 1753 1756 1869 1101 1865 883 755 1210 1220 848 1104 871 720 717 719 0\n1871 -44 -3 0 1753 1758 1789 1756 1865 883 755 1210 140 1220 848 1104 147 187 1648 850 1870 1105 154 1142 245 164 247 165 166 648 1869 1101 299 1157 324 273 170 617 1145 1840 0\n1872 -45 -3 0 1789 1753 1756 1758 1871 1865 883 755 1210 140 1220 848 1104 147 187 1648 850 1870 1105 154 1142 245 164 247 165 166 648 1869 1101 299 1157 324 273 291 1170 296 171 647 1146 149 203 1848 155 1632 950 948 300 76 1161 279 336 0\n1873 -3 0 1789 1753 1754 1755 1758 1756 135 1110 150 1865 291 883 1170 755 296 373 1210 302 1220 848 1648 1104 850 147 204 156 1869 1101 538 1870 1105 154 648 1142 166 1871 907 1872 1836 1811 301 1166 347 285 286 1615 1011 107 0\n1874 111 68 -45 -133 44 20 80 -132 137 129 -141 30 -10 31 0 1789 1757 1220 1648 850 1033 1032 140 1108 1828 1083 69 148 1141 241 244 163 164 1525 1848 0\n1875 -36 103 -132 251 34 -75 -10 -18 0 163 1435 1139 137 0\n1876 -133 111 44 -132 137 -75 -141 -10 -18 0 1757 1761 1756 1755 1754 907 908 147 140 1114 204 156 1003 409 1209 421 963 957 284 384 302 1164 289 618 1135 229 158 150 159 410 657 1199 420 1686 86 1819 1874 0\n1877 -141 -10 -18 83 0 1789 1761 1754 1755 1757 1762 1756 1763 147 140 1114 204 156 1135 1108 227 157 1220 1648 850 229 158 150 159 417 566 1816 962 1205 284 618 1374 1106 390 1552 1164 384 409 1003 1032 1033 289 302 1209 421 963 957 1844 908 907 1875 1525 949 1876 1553 1555 1855 1436 1083 1848 86 1849 101 622 950 954 148 960 208 162 0\n1878 -10 -18 83 0 1789 1753 1754 1755 1756 1763 147 1135 140 1220 1108 1114 1648 227 150 204 850 157 156 1877 1101 1851 908 907 1859 1105 154 849 1833 219 852 1147 162 509 172 259 161 666 171 1148 1836 173 1835 928 1726 655 86 909 0\n1879 -75 -133 12 28 -44 -141 219 26 121 22 0 1761 1790 417 1188 410 437 393 1199 420 609 282 284 657 1225 384 302 1642 1644 35 0\n1880 -133 12 -44 -434 -59 -18 0 1759 1753 147 1121 170 224 156 1126 150 584 788 1101 417 1188 270 1153 275 1163 865 690 571 1211 1135 159 1120 151 410 609 463 437 393 970 1879 1105 402 619 1193 407 465 456 1818 419 387 1819 1351 0\n1881 -45 29 -75 -44 -18 83 0 1759 1753 1756 1762 1790 1878 1102 788 1101 973 509 161 1148 170 257 142 865 690 270 1163 571 98 1257 877 743 1880 1555 1553 147 1135 234 165 417 1205 390 566 1153 1211 1120 151 171 647 1825 238 82 84 1795 162 968 1381 1362 611 1837 11 405 1214 1196 1350 388 0\n1882 29 70 -75 -44 -18 83 0 1790 1759 1753 1756 1761 1762 1760 284 384 302 1175 296 1878 1102 788 1101 973 509 161 1148 170 257 142 865 690 270 1163 571 98 1257 173 147 1121 224 156 666 963 1374 877 743 1880 1555 1553 1126 150 584 1135 234 165 1136 166 417 1205 390 566 1153 1211 1120 151 1881 1861 86 82 83 84 1795 1849 387 527 968 969 285 546 1192 1362 308 400 11 266 405 6 1196 388 0\n1883 -29 137 -75 28 -44 39 72 -141 121 22 0 1761 1760 1756 1790 284 384 302 1175 296 417 1188 157 545 1132 1307 1134 8 10 266 141 1689 308 285 1615 1011 1644 107 35 598 0\n1884 103 71 -101 29 137 129 -75 54 5 12 38 -34 26 121 -59 31 22 0 1759 1753 1790 1756 1762 1760 387 1192 400 284 1175 296 1164 289 270 1163 98 1257 161 1136 166 788 1101 417 1205 566 1153 1837 11 405 1366 1196 981 955 388 969 6 411 548 266 451 308 403 285 99 0\n1885 -75 -44 -18 83 0 1756 1759 1753 1762 1878 1102 788 1101 973 509 877 743 161 1148 170 257 142 1880 1555 1553 147 1121 224 156 1135 234 165 1136 166 417 1205 390 566 270 1163 282 1153 275 865 690 571 1211 159 1120 151 618 1374 1883 1882 1351 387 527 424 398 1884 1362 1552 163 536 1122 1124 148 149 1361 0\n1886 -45 29 -44 -18 83 0 1759 1753 1762 1756 865 1878 1102 690 1885 1105 402 1193 407 619 788 1101 973 509 877 743 161 1148 170 257 142 1880 1555 1553 147 1135 234 417 1205 390 566 270 1153 1211 159 171 1825 238 260 1795 536 162 148 387 1362 1381 456 641 405 69 11 278 287 330 0\n1887 -143 126 284 95 88 28 185 186 -141 211 113 -18 0 1756 1762 1760 414 165 166 417 1205 566 147 1120 151 1804 1849 82 84 1795 285 969 387 527 308 411 546 1192 266 467 400 6 388 0\n1888 -94 137 95 88 28 39 -18 0 1758 1756 301 1166 347 285 1615 1011 909 0\n1889 45 70 284 95 88 28 21 119 185 186 -141 211 113 -18 0 166 414 1888 1836 86 1887 0\n1890 -45 -44 -18 83 0 1759 1753 1756 865 1878 1102 690 1885 1105 402 1193 407 619 788 1101 973 509 877 743 161 1148 170 257 142 1880 147 1135 234 270 1153 1211 159 171 1825 1886 238 260 1795 162 148 532 1381 69 641 0\n1891 -78 71 -101 80 -124 38 -34 251 6 211 31 22 0 1762 387 1192 400 402 1193 407 1203 287 541 531 1167 981 955 266 969 6 411 388 467 0\n1892 -103 -44 -18 83 0 1756 1759 1753 1762 1878 1102 788 1101 417 1205 1211 270 1153 275 973 509 161 1136 147 1135 234 584 170 1126 150 1121 224 156 865 690 1885 1105 652 877 743 1148 257 142 1880 1863 402 1203 1890 1889 1351 387 424 398 1193 407 619 165 390 566 159 1362 1552 163 536 1122 1124 148 149 981 955 76 0\n1893 -44 -18 83 0 1759 1753 1756 1790 1762 147 1135 1878 1102 788 1101 973 509 161 234 165 877 743 1148 1136 417 1205 566 270 1163 282 1153 275 865 690 571 1211 159 1120 151 1121 170 584 1126 224 257 150 156 142 1880 1553 1555 1885 1105 402 652 619 1863 1193 1203 407 1890 1889 1351 387 527 456 405 1891 1892 11 157 543 1122 1307 148 388 981 955 467 969 411 0\n1894 -75 70 28 79 -133 44 194 145 -59 -18 0 1759 1753 1761 1754 1755 1763 788 1101 417 1188 410 437 393 1199 420 124 173 147 1135 159 284 618 963 657 1164 384 289 302 1794 1686 1791 1103 418 1692 1191 1717 1819 443 69 397 0\n1895 70 28 -133 44 -34 -59 -18 0 1756 1759 1753 1754 1755 788 1101 865 690 877 743 417 1188 410 437 970 393 463 147 1135 161 234 1148 666 270 1153 275 1211 159 1894 1105 402 619 1193 407 465 456 1794 419 387 1791 1103 1795 1352 418 1825 1819 1191 1363 443 637 397 69 0\n1896 28 -133 44 -34 -59 -18 0 1759 1753 1761 788 1101 417 410 1199 479 388 463 270 1153 275 865 690 1211 147 1120 151 1895 87 88 90 91 1351 1363 387 527 1193 1192 402 400 454 505 1689 404 284 1423 384 302 0\n1897 -133 44 -34 -59 -18 0 1759 1753 1790 788 1101 417 270 1163 282 571 147 1120 151 410 1199 479 388 1896 156 554 1111 1115 136 141 984 35 271 1212 1154 6 281 0\n1898 -45 29 94 -75 70 -18 83 0 1759 1753 1756 1755 1754 1762 284 1175 296 1164 1374 618 98 1893 1878 1102 788 1101 973 509 417 1188 1897 1360 1103 1692 1791 1555 1553 147 1135 161 234 165 1205 390 566 270 1153 865 690 571 1211 159 1120 151 89 171 1825 238 1795 536 162 527 1362 1805 1884 0\n1899 -12 79 -18 83 0 1759 1753 1755 1754 1756 1893 1878 1102 788 1101 973 509 417 1188 1897 1360 1103 42 45 46 606 1408 1381 0\n1900 29 -75 70 28 -18 83 0 1755 1754 1759 1753 1756 1761 1762 1878 1102 270 1163 284 340 288 1899 788 1101 973 509 161 1148 173 666 963 1374 618 1893 417 1188 1897 1360 1103 1692 1791 1555 1553 147 1135 234 165 1136 1205 390 566 1153 865 690 571 1211 159 1120 151 1898 1861 1795 536 527 1884 1362 0\n1901 -75 70 28 -18 83 0 1759 1753 1755 1754 1761 1790 1760 1756 1893 1878 1102 788 1101 973 509 417 1188 1897 1360 1103 1692 1791 1555 1553 161 1148 173 1136 166 147 1135 234 666 270 1163 282 1153 865 690 571 1211 1120 151 284 1374 963 1175 384 340 296 302 288 1899 1900 17 157 545 1837 1307 8 10 266 1689 308 285 1615 1011 1849 1364 86 1795 1825 0\n1902 70 28 -18 83 0 1759 1753 1755 1754 1762 1756 1893 1878 1102 788 1101 973 509 417 1188 1897 1360 1103 1692 1791 1555 1553 147 1135 161 234 165 1148 1136 1205 390 566 270 1153 865 690 1211 159 1120 151 1901 1105 402 652 619 1863 1193 1203 407 1889 171 1825 238 260 1795 536 162 148 387 527 1362 1381 456 1891 641 405 69 11 532 0\n1903 -103 -75 -101 -18 83 0 1756 1759 1753 1762 1878 1102 788 1101 417 1205 387 424 398 390 973 509 566 1362 1552 163 536 1122 1124 148 149 1361 0\n1904 -75 28 -18 83 0 1759 1753 1761 1760 1756 1878 1102 788 1101 417 1211 270 1153 275 1902 1351 387 1192 454 404 400 527 973 509 1893 1897 1555 1553 147 1135 161 234 165 1136 166 1163 865 690 571 159 1120 151 284 618 1374 1175 384 340 296 302 288 1899 1903 1884 1837 545 6 1689 266 308 285 1615 1011 107 0\n1905 -103 28 -18 83 0 1756 1759 1753 1762 865 1878 1102 690 1904 1105 402 1193 407 619 788 1101 417 1205 1211 270 1153 275 1902 1351 387 424 398 147 1135 973 509 161 234 165 390 566 159 1362 1552 163 536 1122 1124 148 149 981 955 76 0\n1906 28 -18 83 0 1756 1759 1753 1790 1762 1878 1102 788 1101 973 509 1893 1897 1555 1553 147 1135 161 234 165 417 1205 566 270 1163 282 1153 275 865 690 571 1211 159 1120 151 1902 1351 387 527 1192 1904 1105 402 619 1891 1193 1203 448 407 405 1905 11 157 543 1122 1307 148 388 981 955 467 969 411 0\n1907 -75 29 -18 83 0 1790 1759 1753 1756 1755 1754 1762 1878 1102 571 270 1163 282 1893 788 1101 973 509 417 1188 1897 1360 1103 1906 597 156 1115 141 35 392 1197 406 147 1120 151 554 1111 136 984 1555 1553 161 1136 166 1205 390 566 284 1374 589 1175 340 296 288 1556 1899 1362 1598 0\n1908 29 -18 83 0 1790 1755 1754 1759 1753 1762 1756 1873 147 1120 151 1878 1102 788 1101 1906 554 156 1111 136 571 270 1163 282 1893 973 509 417 1188 1897 1360 1103 597 1115 141 35 984 388 1196 405 418 1206 392 433 403 1213 1555 1553 1135 161 234 165 1136 166 1205 390 566 1153 275 865 690 1211 159 1907 1105 402 652 619 1203 414 467 1556 411 1362 1411 11 1495 1891 1162 1100 265 0\n1909 -18 83 0 1759 1753 1754 1755 1790 1762 1756 1873 147 865 1120 1135 151 159 1878 1102 270 1211 788 571 690 1153 1163 1101 275 282 417 566 973 1188 1205 509 161 1136 234 166 165 1893 1897 1360 1103 418 1206 1906 156 554 597 1111 1115 136 141 35 392 984 433 388 403 1908 157 545 1122 1105 148 402 652 619 1193 1203 407 414 467 981 955 1556 411 969 1411 1100 1495 265 1162 0\n1910 83 0 1789 1909 501 848 867 977 1220 869 1102 709 697 1106 699 0\n1911 -34 0 1910 119 0\n1912 230 0 1910 291 0\n1913 445 0 1910 883 0\n1914 -235 0 1912 1170 0\n1915 -201 0 1912 1760 310 0\n1916 231 0 1912 1758 358 0\n1917 -59 0 1913 1756 755 0\n1918 -88 0 1914 296 0\n1919 -242 0 1914 1758 373 0\n1920 -54 0 1915 267 0\n1921 10 0 1917 1210 0\n1922 -95 0 1919 302 0\n1923 157 0 1921 140 0\n1924 296 0 1921 1220 0\n1925 150 0 1923 1108 0\n1926 -168 0 1923 1114 0\n1927 -116 0 1924 848 0\n1928 297 0 1924 1789 1648 0\n1929 -21 0 1926 150 0\n1930 18 0 1927 1789 1104 0\n1931 -124 0 1928 850 0\n1932 165 0 1930 147 0\n1933 -178 0 1932 1135 0\n1934 158 0 1932 1923 187 0\n1935 151 0 1932 1925 179 0\n1936 -175 0 1932 1926 204 0\n1937 -31 0 1933 159 0\n1938 -177 0 1933 1923 229 0\n1939 -176 0 1933 1925 227 0\n1940 -28 0 1936 156 0\n1941 -30 0 1938 158 0\n1942 -29 0 1939 157 0\n1943 -5 -75 -141 0 1916 1920 1756 1757 1912 1929 1942 1754 1755 1762 1930 1921 1911 1910 284 1164 361 301 957 356 295 289 618 96 417 1205 390 566 13 15 556 1012 1411 1525 949 293 1156 321 272 1839 1824 907 398 578 170 1190 1145 412 143 975 1716 142 0\n1944 -75 -141 0 1912 1916 1756 1929 1941 1920 1942 1937 1754 1755 1757 1930 1921 1911 1910 1762 417 1205 390 566 96 284 618 1164 289 356 361 295 301 957 1943 1838 1839 1398 907 1525 949 170 1824 1145 398 578 143 1190 1716 412 142 975 0\n1945 -141 0 1931 1910 1932 1934 1935 1930 1756 1757 1762 1754 1755 1929 1922 1918 1921 1940 417 566 1205 390 1944 1105 154 648 1142 166 247 245 242 1888 165 164 163 957 1525 949 1830 1145 170 907 1841 0\n1946 92 0 1945 1753 1101 0\n1947 239 0 1946 299 0\n1948 -210 0 1947 1157 0\n1949 -209 0 1948 1758 324 0\n1950 -62 0 1949 273 0\n1951 -75 0 1946 1921 1910 1756 1930 871 720 717 719 0\n1952 26 0 1951 1931 1105 0\n1953 173 0 1952 154 0\n1954 -137 0 1952 1910 648 0\n1955 -186 0 1953 1142 0\n1956 -39 0 1955 166 0\n1957 -185 0 1955 1932 247 0\n1958 -184 0 1955 1934 245 0\n1959 -94 0 1956 1922 1918 1940 1954 1930 1888 0\n1960 -38 0 1957 165 0\n1961 -37 0 1958 164 0\n1962 -44 0 1756 1910 1954 1956 1960 1950 1961 170 617 1145 1840 0\n1963 -119 0 1962 1755 1921 1754 908 0\n1964 -70 0 1962 1755 1921 1754 907 0\n1965 126 0 1963 1950 1954 1918 1955 1962 1921 1959 1922 1940 1929 1809 0\n1966 45 0 1965 1963 1964 1930 1940 1929 1836 0\n1967 192 0 1966 171 0\n1968 -118 0 1966 1756 647 0\n1969 -167 0 1967 1146 0\n1970 -20 0 1969 149 0\n1971 -174 0 1969 1932 203 0\n1972 111 0 1970 1950 1956 1960 1961 1962 1966 1918 1954 1921 1848 0\n1973 -27 0 1971 155 0\n1974 93 0 1972 1756 1753 1632 0\n1975 -87 0 1973 1956 1930 1954 1918 950 0\n1976 -136 0 1973 1918 1956 1954 1930 948 0\n1977 240 0 1974 300 0\n1978 69 0 1975 1976 1960 1968 1970 76 0\n1979 -217 0 1977 1161 0\n1980 216 0 1978 279 0\n1981 0 1979 1980 1758 336 0\n"

theorem raw_n7_root (word : Fin 7 → Fin 3) :
    ClauseProof (fun val => ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val ∧ True) Sat.Clause.nil := by
  intro val hh
  have h := hh.left
  have bad := cert_n7_root (val 0) (val 1) (val 2) (val 3) (val 4) (val 5) (val 6) (val 7) (val 8) (val 9) (val 10) (val 11) (val 12) (val 13) (val 14) (val 15) (val 16) (val 17) (val 18) (val 19) (val 20) (val 21) (val 22) (val 23) (val 24) (val 25) (val 26) (val 27) (val 28) (val 29) (val 30) (val 31) (val 32) (val 33) (val 34) (val 35) (val 36) (val 37) (val 38) (val 39) (val 40) (val 41) (val 42) (val 43) (val 44) (val 45) (val 46) (val 47) (val 48) (val 49) (val 50) (val 51) (val 52) (val 53) (val 54) (val 55) (val 56) (val 57) (val 58) (val 59) (val 60) (val 61) (val 62) (val 63) (val 64) (val 65) (val 66) (val 67) (val 68) (val 69) (val 70) (val 71) (val 72) (val 73) (val 74) (val 75) (val 76) (val 77) (val 78) (val 79) (val 80) (val 81) (val 82) (val 83) (val 84) (val 85) (val 86) (val 87) (val 88) (val 89) (val 90) (val 91) (val 92) (val 93) (val 94) (val 95) (val 96) (val 97) (val 98) (val 99) (val 100) (val 101) (val 102) (val 103) (val 104) (val 105) (val 106) (val 107) (val 108) (val 109) (val 110) (val 111) (val 112) (val 113) (val 114) (val 115) (val 116) (val 117) (val 118) (val 119) (val 120) (val 121) (val 122) (val 123) (val 124) (val 125) (val 126) (val 127) (val 128) (val 129) (val 130) (val 131) (val 132) (val 133) (val 134) (val 135) (val 136) (val 137) (val 138) (val 139) (val 140) (val 141) (val 142) (val 143) (val 144) (val 145) (val 146) (val 147) (val 148) (val 149) (val 150) (val 151) (val 152) (val 153) (val 154) (val 155) (val 156) (val 157) (val 158) (val 159) (val 160) (val 161) (val 162) (val 163) (val 164) (val 165) (val 166) (val 167) (val 168) (val 169) (val 170) (val 171) (val 172) (val 173) (val 174) (val 175) (val 176) (val 177) (val 178) (val 179) (val 180) (val 181) (val 182) (val 183) (val 184) (val 185) (val 186) (val 187) (val 188) (val 189) (val 190) (val 191) (val 192) (val 193) (val 194) (val 195) (val 196) (val 197) (val 198) (val 199) (val 200) (val 201) (val 202) (val 203) (val 204) (val 205) (val 206) (val 207) (val 208) (val 209) (val 210) (val 211) (val 212) (val 213) (val 214) (val 215) (val 216) (val 217) (val 218) (val 219) (val 220) (val 221) (val 222) (val 223) (val 224) (val 225) (val 226) (val 227) (val 228) (val 229) (val 230) (val 231) (val 232) (val 233) (val 234) (val 235) (val 236) (val 237) (val 238) (val 239) (val 240) (val 241) (val 242) (val 243) (val 244) (val 245) (val 246) (val 247) (val 248) (val 249) (val 250) (val 251) (val 252) (val 253) (val 254) (val 255) (val 256) (val 257) (val 258) (val 259) (val 260) (val 261) (val 262) (val 263) (val 264) (val 265) (val 266) (val 267) (val 268) (val 269) (val 270) (val 271) (val 272) (val 273) (val 274) (val 275) (val 276) (val 277) (val 278) (val 279) (val 280) (val 281) (val 282) (val 283) (val 284) (val 285) (val 286) (val 287) (val 288) (val 289) (val 290) (val 291) (val 292) (val 293) (val 294) (val 295) (val 296) (val 297) (val 298) (val 299) (val 300) (val 301) (val 302) (val 303) (val 304) (val 305) (val 306) (val 307) (val 308) (val 309) (val 310) (val 311) (val 312) (val 313) (val 314) (val 315) (val 316) (val 317) (val 318) (val 319) (val 320) (val 321) (val 322) (val 323) (val 324) (val 325) (val 326) (val 327) (val 328) (val 329) (val 330) (val 331) (val 332) (val 333) (val 334) (val 335) (val 336) (val 337) (val 338) (val 339) (val 340) (val 341) (val 342) (val 343) (val 344) (val 345) (val 346) (val 347) (val 348) (val 349) (val 350) (val 351) (val 352) (val 353) (val 354) (val 355) (val 356) (val 357) (val 358) (val 359) (val 360) (val 361) (val 362) (val 363) (val 364) (val 365) (val 366) (val 367) (val 368) (val 369) (val 370) (val 371) (val 372) (val 373) (val 374) (val 375) (val 376) (val 377) (val 378) (val 379) (val 380) (val 381) (val 382) (val 383) (val 384) (val 385) (val 386) (val 387) (val 388) (val 389) (val 390) (val 391) (val 392) (val 393) (val 394) (val 395) (val 396) (val 397) (val 398) (val 399) (val 400) (val 401) (val 402) (val 403) (val 404) (val 405) (val 406) (val 407) (val 408) (val 409) (val 410) (val 411) (val 412) (val 413) (val 414) (val 415) (val 416) (val 417) (val 418) (val 419) (val 420) (val 421) (val 422) (val 423) (val 424) (val 425) (val 426) (val 427) (val 428) (val 429) (val 430) (val 431) (val 432) (val 433) (val 434) (val 435) (val 436) (val 437) (val 438) (val 439) (val 440) (val 441) (val 442) (val 443) (val 444) (val 445) (val 446) (val 447) (val 448) (val 449) (val 450) (val 451) (val 452) (val 453) (val 454) (val 455) (val 456) (val 457) (val 458) (val 459) (val 460) (val 461) (val 462) (val 463) (val 464) (val 465) (val 466) (val 467) (val 468) (val 469) (val 470) (val 471) (val 472) (val 473) (val 474) (val 475) (val 476) (val 477) (val 478) (val 479) (val 480) (val 481) (val 482) (val 483) (val 484) (val 485) (val 486) (val 487) (val 488) (val 489) (val 490) (val 491) (val 492) (val 493) (val 494) (val 495) (val 496) (val 497) (val 498) (val 499) (val 500) (val 501) (val 502) (val 503) (val 504) (val 505) (val 506) (val 507) (val 508) (val 509) (val 510) (val 511) (val 512) (val 513) (val 514) (val 515) (val 516) (val 517) (val 518) (val 519) (val 520) (val 521) (val 522) (val 523) (val 524) (val 525) (val 526) (val 527) (val 528) (val 529) (val 530) (val 531) (val 532) (val 533) (val 534) (val 535) (val 536) (val 537) (val 538) (val 539)
  exact Or.elim (bad)
    (fun badL0 => Or.elim (badL0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c0 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c1 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c2 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c3 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c4 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c5 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c6 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c7 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c8 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c9 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c10 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c11 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c12 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c13 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c14 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c15 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c16 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c17 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c18 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c19 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c20 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c21 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c22 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c23 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c24 word val h (badR9.1) (badR9.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c25 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c26 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c27 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c28 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c29 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c30 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c31 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c32 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c33 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c34 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c35 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c36 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c37 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c38 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c39 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c40 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c41 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c42 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c43 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c44 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c45 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c46 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c47 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c48 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c49 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c50 word val h (badR9.1) (badR9.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c51 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c52 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c53 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c54 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c55 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c56 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c57 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c58 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c59 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c60 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c61 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c62 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c63 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c64 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c65 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c66 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c67 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c68 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c69 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c70 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c71 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c72 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c73 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c74 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c75 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c76 word val h (badR9.1) (badR9.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c77 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c78 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c79 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c80 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c81 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c82 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c83 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c84 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c85 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c86 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c87 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c88 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c89 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c90 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c91 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c92 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c93 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c94 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2.1) (badL9.2.2.2.2.1) (badL9.2.2.2.2.2))
    (fun badR9 => input_n7_c95 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c96 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c97 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c98 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c99 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c100 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c101 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c102 word val h (badR9.1) (badR9.2)))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c103 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c104 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c105 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c106 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c107 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c108 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c109 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c110 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c111 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c112 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c113 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c114 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c115 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c116 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c117 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2.1) (badR9.2.2.2.2.1) (badR9.2.2.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c118 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c119 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c120 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c121 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c122 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c123 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c124 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c125 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c126 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c127 word val h (badR9.1) (badR9.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c128 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c129 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c130 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c131 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2.1) (badL8.2.2.2.2.1) (badL8.2.2.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c132 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c133 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c134 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c135 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c136 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c137 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c138 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c139 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c140 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c141 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c142 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c143 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c144 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c145 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c146 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c147 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c148 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c149 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c150 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c151 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c152 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c153 word val h (badR9.1) (badR9.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c154 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c155 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c156 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c157 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c158 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c159 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c160 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c161 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c162 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c163 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c164 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c165 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c166 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c167 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c168 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c169 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c170 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c171 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c172 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c173 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c174 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c175 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c176 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c177 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c178 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c179 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c180 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c181 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c182 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c183 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c184 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c185 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c186 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c187 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c188 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c189 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c190 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c191 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c192 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c193 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c194 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c195 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c196 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c197 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c198 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c199 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c200 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c201 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c202 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c203 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c204 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c205 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c206 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c207 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c208 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c209 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c210 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c211 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c212 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c213 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c214 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c215 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c216 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c217 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c218 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c219 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c220 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c221 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c222 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c223 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c224 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c225 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c226 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c227 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c228 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c229 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c230 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c231 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c232 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c233 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c234 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c235 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c236 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c237 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c238 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c239 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c240 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c241 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c242 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c243 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c244 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c245 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c246 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c247 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c248 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c249 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c250 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c251 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c252 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c253 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c254 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c255 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c256 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c257 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c258 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c259 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c260 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c261 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c262 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c263 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c264 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c265 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c266 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c267 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c268 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c269 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c270 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c271 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c272 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c273 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c274 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c275 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c276 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c277 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c278 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c279 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c280 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c281 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c282 word val h (badR9.1) (badR9.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c283 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c284 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c285 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c286 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c287 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c288 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c289 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c290 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c291 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c292 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c293 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c294 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c295 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c296 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c297 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c298 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c299 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c300 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c301 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c302 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c303 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c304 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c305 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c306 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c307 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c308 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c309 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c310 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c311 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c312 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c313 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c314 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c315 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c316 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c317 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c318 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c319 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c320 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c321 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c322 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c323 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c324 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c325 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c326 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c327 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c328 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c329 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c330 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c331 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c332 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c333 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c334 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c335 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c336 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c337 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c338 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c339 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c340 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c341 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c342 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c343 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c344 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c345 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c346 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c347 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c348 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c349 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c350 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c351 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c352 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c353 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c354 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c355 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c356 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c357 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c358 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c359 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c360 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c361 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c362 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c363 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c364 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c365 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c366 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c367 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c368 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c369 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c370 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c371 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c372 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c373 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c374 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c375 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c376 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c377 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c378 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c379 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c380 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c381 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c382 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c383 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c384 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c385 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c386 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c387 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c388 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c389 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c390 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c391 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c392 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c393 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c394 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c395 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c396 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c397 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c398 word val h (badR9.1) (badR9.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c399 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c400 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c401 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c402 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c403 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c404 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c405 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c406 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c407 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c408 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c409 word val h (badR9.1) (badR9.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c410 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c411 word val h (badR9.1) (badR9.2)))))))))))
    (fun badR0 => Or.elim (badR0)
    (fun badL1 => Or.elim (badL1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c412 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c413 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c414 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c415 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c416 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c417 word val h (badR9.1) (badR9.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c418 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c419 word val h (badL9.1) (badL9.2))
    (fun badR9 => input_n7_c420 word val h (badR9.1) (badR9.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c421 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c422 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c423 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c424 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c425 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c426 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c427 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c428 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c429 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c430 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c431 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c432 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c433 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c434 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c435 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c436 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c437 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c438 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c439 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c440 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c441 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c442 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c443 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c444 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c445 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c446 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c447 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c448 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c449 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c450 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c451 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c452 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c453 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c454 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c455 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c456 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c457 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c458 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c459 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c460 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c461 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c462 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c463 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c464 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c465 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c466 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c467 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c468 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c469 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c470 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c471 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c472 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c473 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c474 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c475 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c476 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c477 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c478 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c479 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c480 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c481 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c482 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c483 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c484 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c485 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c486 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c487 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c488 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c489 word val h (badL8))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c490 word val h (badL9))
    (fun badR9 => input_n7_c491 word val h (badR9))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c492 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c493 word val h (badL9))
    (fun badR9 => input_n7_c494 word val h (badR9)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c495 word val h (badL8))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c496 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c497 word val h (badR9))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c498 word val h (badL9))
    (fun badR9 => input_n7_c499 word val h (badR9)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c500 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c501 word val h (badR9))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c502 word val h (badL8))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c503 word val h (badL9))
    (fun badR9 => input_n7_c504 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c505 word val h (badL8))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c506 word val h (badL9))
    (fun badR9 => input_n7_c507 word val h (badR9)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c508 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c509 word val h (badL9))
    (fun badR9 => input_n7_c510 word val h (badR9))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c511 word val h (badL9))
    (fun badR9 => input_n7_c512 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c513 word val h (badL9))
    (fun badR9 => input_n7_c514 word val h (badR9)))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c515 word val h (badL8))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c516 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c517 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c518 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c519 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c520 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c521 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c522 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c523 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c524 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c525 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c526 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c527 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c528 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c529 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c530 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c531 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c532 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c533 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c534 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c535 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c536 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c537 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c538 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c539 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c540 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c541 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c542 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c543 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c544 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c545 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c546 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c547 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c548 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c549 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c550 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c551 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c552 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c553 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c554 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c555 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c556 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c557 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c558 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c559 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c560 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c561 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c562 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c563 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c564 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c565 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c566 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c567 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c568 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c569 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c570 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c571 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c572 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c573 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c574 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c575 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c576 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c577 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c578 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c579 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c580 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c581 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c582 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c583 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c584 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c585 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c586 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c587 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c588 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c589 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c590 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c591 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c592 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c593 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c594 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c595 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c596 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c597 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c598 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c599 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c600 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c601 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c602 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c603 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c604 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c605 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c606 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c607 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c608 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c609 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c610 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c611 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c612 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c613 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c614 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c615 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c616 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c617 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))))
    (fun badR1 => Or.elim (badR1)
    (fun badL2 => Or.elim (badL2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c618 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c619 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c620 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c621 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c622 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c623 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c624 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c625 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c626 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c627 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c628 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c629 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c630 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c631 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c632 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c633 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c634 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c635 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c636 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c637 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c638 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c639 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c640 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c641 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c642 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c643 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c644 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c645 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c646 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c647 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c648 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c649 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c650 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c651 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c652 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c653 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c654 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c655 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c656 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c657 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c658 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c659 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c660 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c661 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c662 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c663 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c664 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c665 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c666 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c667 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c668 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c669 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c670 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c671 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c672 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c673 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c674 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c675 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c676 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c677 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c678 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c679 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c680 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c681 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c682 word val h (badL8.1) (badL8.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c683 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c684 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c685 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c686 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c687 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c688 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c689 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c690 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c691 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c692 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c693 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c694 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c695 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c696 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c697 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c698 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c699 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c700 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c701 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c702 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c703 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c704 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c705 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c706 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c707 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c708 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c709 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c710 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c711 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c712 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c713 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c714 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c715 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c716 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c717 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c718 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c719 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c720 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))))
    (fun badR2 => Or.elim (badR2)
    (fun badL3 => Or.elim (badL3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c721 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c722 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c723 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c724 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c725 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c726 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c727 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c728 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c729 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c730 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c731 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c732 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c733 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c734 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c735 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c736 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c737 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c738 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c739 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c740 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c741 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c742 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c743 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c744 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c745 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c746 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c747 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c748 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c749 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c750 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c751 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c752 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c753 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c754 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c755 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c756 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c757 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c758 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c759 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c760 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c761 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c762 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c763 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c764 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c765 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c766 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c767 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c768 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c769 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c770 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c771 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))))
    (fun badR3 => Or.elim (badR3)
    (fun badL4 => Or.elim (badL4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c772 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c773 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c774 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c775 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c776 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c777 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c778 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c779 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c780 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c781 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c782 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c783 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c784 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c785 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c786 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c787 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c788 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c789 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c790 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c791 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c792 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c793 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c794 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c795 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c796 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c797 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))))
    (fun badR4 => Or.elim (badR4)
    (fun badL5 => Or.elim (badL5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c798 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c799 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c800 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c801 word val h (badL8.1) (badL8.2.1) (badL8.2.2.1) (badL8.2.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c802 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c803 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c804 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c805 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c806 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c807 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c808 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c809 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c810 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))))
    (fun badR5 => Or.elim (badR5)
    (fun badL6 => Or.elim (badL6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c811 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c812 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c813 word val h (badR9.1) (badR9.2.1) (badR9.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => input_n7_c814 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c815 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c816 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2)))))
    (fun badR6 => Or.elim (badR6)
    (fun badL7 => Or.elim (badL7)
    (fun badL8 => input_n7_c817 word val h (badL8.1) (badL8.2.1) (badL8.2.2))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c818 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c819 word val h (badR9.1) (badR9.2.1) (badR9.2.2.1) (badR9.2.2.2))))
    (fun badR7 => Or.elim (badR7)
    (fun badL8 => Or.elim (badL8)
    (fun badL9 => input_n7_c820 word val h (badL9.1) (badL9.2.1) (badL9.2.2))
    (fun badR9 => input_n7_c821 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))
    (fun badR8 => Or.elim (badR8)
    (fun badL9 => input_n7_c822 word val h (badL9.1) (badL9.2.1) (badL9.2.2.1) (badL9.2.2.2))
    (fun badR9 => input_n7_c823 word val h (badR9.1) (badR9.2.1) (badR9.2.2)))))))))))

theorem exclude_n7_root (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) (_hp : True) : False :=
  raw_n7_root word val ⟨h, True.intro⟩

theorem universal_n7_root (word : Fin 7 → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot 7) lexPerm val) : False :=
  raw_n7_root word val ⟨h, True.intro⟩
end OPG1808SmallOrders


-- Bundled whole source: OrdersUpTo7.lean

namespace OPG1808SmallOrders
open ModuleOPG1808Certificate
theorem universal_up_to_7 (m : ℕ) [NeZero m] [NeZero (m - 1)]
    (hm3 : 3 ≤ m) (hmBound : m ≤ 7) (word : Fin m → Fin 3) (val : Sat.Valuation)
    (h : ModuleOPG1808CNF.LexModel word (lexRot m) lexPerm val) : False := by
  interval_cases m
  · exact universal_n3_root word val h
  · exact universal_n4_root word val h
  · exact universal_n5_root word val h
  · exact universal_n6_root word val h
  · exact universal_n7_root word val h
end OPG1808SmallOrders

-- Bundled whole source: CNFSemantics.lean

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

-- Bundled whole source: CNFClauses.lean

namespace OPG1808CNF.Model

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

end OPG1808CNF.Model

-- Bundled whole source: LexSemantics.lean

namespace OPG1808CNF

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

end OPG1808CNF

-- Bundled whole source: LegacyBridge.lean

namespace ModuleBridgeBenchmark

theorem model_transport {n : ℕ} {word : Fin n → Fin 3} {val : Sat.Valuation}
    (h : OPG1808CNF.Model word val) : ModuleOPG1808CNF.Model word val :=
  { orientation := h.orientation
    color_exclusive := h.color_exclusive
    direction_exclusive := h.direction_exclusive
    arc_reach := h.arc_reach
    reach_trans := h.reach_trans
    predecessor_forbidden := h.predecessor_forbidden
    cycle := h.cycle
    rainbow_forbidden := h.rainbow_forbidden }

theorem lexModel_transport {n : ℕ} [NeZero n] [NeZero (n - 1)]
    {word : Fin n → Fin 3} {rot : ℕ → Fin n} {perm : ℕ → Equiv.Perm (Fin 3)}
    {val : Sat.Valuation} (h : OPG1808CNF.LexModel word rot perm val) :
    ModuleOPG1808CNF.LexModel word rot perm val :=
  { toModel := model_transport h.toModel
    prefix_eq := h.prefix_eq
    minimal := h.minimal }


end ModuleBridgeBenchmark

-- Bundled whole source: FiniteCycle.lean

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

-- Bundled whole source: NoSourceCycle.lean

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

-- Bundled whole source: ColorNormalization.lean

open OPG1808

namespace OPG1808Audit

universe u

/-- Every rotation/palette orbit contains a word of minimal natural-valued rank.
Its rank is minimal even when the orbit is computed again from that word. -/
theorem exists_rotation_color_rank_min {n : ℕ} [NeZero n]
    (w : Fin n → Fin 3) (rank : (Fin n → Fin 3) → ℕ) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        rank w' ≤ rank (fun i ↦ τ (w' (i + s))) := by
  classical
  let P : ℕ → Prop := fun k ↦
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3), rank (fun i ↦ σ (w (i + r))) = k
  have hex : ∃ k, P k := by
    refine ⟨rank w, 0, Equiv.refl _, ?_⟩
    simp only [add_zero, Equiv.refl_apply]
  obtain ⟨r, σ, hmin⟩ := Nat.find_spec hex
  refine ⟨r, σ, ?_⟩
  dsimp only
  intro s τ
  rw [hmin]
  apply Nat.find_min' hex
  refine ⟨s + r, σ.trans τ, ?_⟩
  congr 1
  funext i
  simp only [Equiv.trans_apply, add_assoc]

/-- A bijection of the palette preserves monochromatic reachability exactly. -/
theorem monochromatically_reaches_color_equiv {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (σ : Equiv.Perm (Fin 3)) (s t : V) :
    MonochromaticallyReaches D (fun x y ↦ σ (color x y)) s t ↔
      MonochromaticallyReaches D color s t := by
  constructor
  · rintro ⟨k, hpath⟩
    refine ⟨σ.symm k, Relation.ReflTransGen.mono ?_ s t hpath⟩
    intro x y h
    refine ⟨h.1, σ.injective ?_⟩
    simpa only [Equiv.apply_symm_apply] using h.2
  · rintro ⟨k, hpath⟩
    refine ⟨σ k, Relation.ReflTransGen.mono ?_ s t hpath⟩
    intro x y h
    exact ⟨h.1, congrArg σ h.2⟩

/-- Relabelling colors, even non-injectively, cannot create a rainbow triangle. -/
theorem no_rainbow_color_map {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (σ : Fin 3 → Fin 3)
    (h : ¬HasRainbowDirectedTriangle D color) :
    ¬HasRainbowDirectedTriangle D (fun x y ↦ σ (color x y)) := by
  rintro ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, hCab, hCbc, hCca⟩
  apply h
  refine ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, ?_, ?_, ?_⟩
  · exact fun hc ↦ hCab (congrArg σ hc)
  · exact fun hc ↦ hCbc (congrArg σ hc)
  · exact fun hc ↦ hCca (congrArg σ hc)

/-- The color of any selected arc can be changed to zero without changing
monochromatic reachability or absence of rainbow directed triangles. -/
theorem exists_color_normalization {V : Type u}
    (D : Digraph V) (color : ArcColoring V) (a b : V) :
    ∃ σ : Equiv.Perm (Fin 3), σ (color a b) = 0 ∧
      (∀ s t : V,
        MonochromaticallyReaches D (fun x y ↦ σ (color x y)) s t ↔
          MonochromaticallyReaches D color s t) ∧
      (¬HasRainbowDirectedTriangle D color →
        ¬HasRainbowDirectedTriangle D (fun x y ↦ σ (color x y))) := by
  refine ⟨Equiv.swap (color a b) 0, ?_, ?_, ?_⟩
  · exact Equiv.swap_apply_left _ _
  · exact monochromatically_reaches_color_equiv D color _
  · exact no_rainbow_color_map D color _

end OPG1808Audit

-- Bundled whole source: LexNormalization.lean

namespace OPG1808Audit

universe v

/-- Every rotation/palette orbit contains a word minimizing any linearly ordered rank. -/
theorem exists_rotation_color_rank_min_linear_order {n : ℕ} [NeZero n]
    {α : Type v} [LinearOrder α] (w : Fin n → Fin 3)
    (rank : (Fin n → Fin 3) → α) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        rank w' ≤ rank (fun i ↦ τ (w' (i + s))) := by
  classical
  obtain ⟨p, hmin⟩ := Finite.exists_min (fun p : Fin n × Equiv.Perm (Fin 3) ↦
    rank (fun i ↦ p.2 (w (i + p.1))))
  refine ⟨p.1, p.2, ?_⟩
  dsimp only
  intro s τ
  simpa only [Equiv.trans_apply, add_assoc] using hmin (s + p.1, p.2.trans τ)

/-- A rotation/palette orbit contains a word below each of its transforms in lex order. -/
theorem exists_rotation_color_lex_min {n : ℕ} [NeZero n] (w : Fin n → Fin 3) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3),
        toLex w' ≤ toLex (fun i ↦ τ (w' (i + s))) :=
  exists_rotation_color_rank_min_linear_order w toLex

/-- A lex-minimal orbit representative satisfies every equal-prefix digit comparison. -/
theorem exists_rotation_color_prefix_min {n : ℕ} [NeZero n] (w : Fin n → Fin 3) :
    ∃ r : Fin n, ∃ σ : Equiv.Perm (Fin 3),
      let w' : Fin n → Fin 3 := fun i ↦ σ (w (i + r))
      ∀ s : Fin n, ∀ τ : Equiv.Perm (Fin 3), ∀ i : Fin n,
        (∀ j : Fin n, j < i → w' j = τ (w' (j + s))) → w' i ≤ τ (w' (i + s)) := by
  obtain ⟨r, σ, hmin⟩ := exists_rotation_color_lex_min w
  refine ⟨r, σ, ?_⟩
  dsimp only at hmin ⊢
  intro s τ i hprefix
  exact Pi.apply_le_of_toLex (hmin s τ) hprefix

end OPG1808Audit

-- Bundled whole source: CycleNormalization.lean

open OPG1808

namespace OPG1808Audit

universe u

/-- A finite no-source tournament restricts and relabels to a lex-normalized cyclic
obstruction. Every hypothesis is inherited from the original tournament. -/
theorem normalized_obstruction_of_no_source
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (ht : IsTournament D) (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hnosource : ¬∃ s : V, IsMonochromaticSource D color s) :
    ∃ m : ℕ, 3 ≤ m ∧ m ≤ Fintype.card V ∧
      ∃ D' : Digraph (Fin m), ∃ color' : ArcColoring (Fin m),
        IsTournament D' ∧ ¬HasRainbowDirectedTriangle D' color' ∧
        (∀ i : Fin m, D' i (finRotate m i) ∧
          ¬MonochromaticallyReaches D' color' (finRotate m i) i) ∧
        (∀ r : Fin m, ∀ σ : Equiv.Perm (Fin 3),
          letI : NeZero m := r.neZero
          toLex (fun i ↦ color' i (finRotate m i)) ≤
            toLex (fun i ↦ σ (color' (i + r) (finRotate m (i + r))))) := by
  classical
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ :=
    missing_predecessor_cycle_of_no_source D color ht hnosource
  let inst : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hm)⟩
  let w : Fin m → Fin 3 := fun i ↦ color (e i) (e (finRotate m i))
  obtain ⟨r, σ, hmin⟩ := exists_rotation_color_lex_min w
  dsimp only at hmin
  let e' : Fin m → V := fun i ↦ e (i + r)
  let D' : Digraph (Fin m) := fun i j ↦ D (e' i) (e' j)
  let color' : ArcColoring (Fin m) := fun i j ↦ σ (color (e' i) (e' j))
  have he' : Function.Injective e' := by
    intro i j hij
    exact add_right_cancel (he hij)
  have hrot : ∀ i : Fin m, finRotate m (i + r) = finRotate m i + r := by
    intro i
    simp only [finRotate_apply]
    ac_rfl
  have hword : ∀ i : Fin m, color' i (finRotate m i) = σ (w (i + r)) := by
    intro i
    change σ (color (e (i + r)) (e (finRotate m i + r))) =
      σ (color (e (i + r)) (e (finRotate m (i + r))))
    rw [hrot]
  refine ⟨m, hm, hcard, D', color', is_tournament_map D e' he' ht, ?_, ?_, ?_⟩
  · exact no_rainbow_color_map D' (fun i j ↦ color (e' i) (e' j)) σ
      (no_rainbow_map D color e' he' hnoRainbow)
  · intro i
    have hc := hcycle (i + r)
    constructor
    · change D (e (i + r)) (e (finRotate m i + r))
      simpa only [hrot] using hc.1
    · intro hpath
      have hpath0 : MonochromaticallyReaches D'
          (fun a b ↦ color (e' a) (e' b)) (finRotate m i) i :=
        (monochromatically_reaches_color_equiv D' (fun a b ↦ color (e' a) (e' b))
          σ _ _).mp hpath
      have horig := monochromatically_reaches_map D color e' hpath0
      apply hc.2
      simpa only [e', hrot] using horig
  · intro s τ
    simpa only [hword] using hmin s τ

end OPG1808Audit

-- Bundled whole source: PhysicalUpTo7.lean

open OPG1808
namespace OPG1808SmallOrders
universe u

theorem source_up_to_7 {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V) (ht : IsTournament D)
    (hbound : Fintype.card V ≤ 7) (hno : ¬HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  classical
  by_contra hnosource
  obtain ⟨m, hm, hcard, D', color', ht', hno', hcycle, hmin⟩ :=
    OPG1808Audit.normalized_obstruction_of_no_source D color ht hno hnosource
  let inst : NeZero m := ⟨by omega⟩
  let instPred : NeZero (m - 1) := ⟨by omega⟩
  let word : Fin m → Fin 3 := fun i ↦ color' i (finRotate m i)
  have hphysical : OPG1808CNF.Model word (OPG1808CNF.physicalVal D' color') :=
    OPG1808CNF.physical_model D' color' word ht' hno'
      (fun i ↦ ⟨(hcycle i).1, rfl⟩) (fun i ↦ (hcycle i).2)
  have hprefix : OPG1808CNF.PrefixMinimal word := by
    intro r σ i hp
    exact Pi.apply_le_of_toLex (hmin r σ) hp
  exact universal_up_to_7 m hm (hcard.trans hbound) word
    (OPG1808CNF.extendedVal word (ModuleOPG1808Certificate.lexRot m)
      ModuleOPG1808Certificate.lexPerm (OPG1808CNF.physicalVal D' color'))
    (ModuleBridgeBenchmark.lexModel_transport
      (OPG1808CNF.extended_model hphysical hprefix
        (ModuleOPG1808Certificate.lexRot m) ModuleOPG1808Certificate.lexPerm))

theorem return_up_to_7 (m : ℕ) (hm3 : 3 ≤ m) (hmBound : m ≤ 7)
    (D : Digraph (Fin m)) (color : ArcColoring (Fin m))
    (ht : IsTournament D) (hno : ¬HasRainbowDirectedTriangle D color) :
    ∃ i : Fin m, MonochromaticallyReaches D color (finRotate m i) i := by
  let inst : NeZero m := ⟨by omega⟩
  obtain ⟨s, hs⟩ := source_up_to_7 D color ht (by simpa only [Fintype.card_fin] using hmBound) hno
  obtain ⟨i, hi⟩ := (finRotate m).surjective s
  exact ⟨i, by simpa only [hi] using hs i⟩

end OPG1808SmallOrders

open OPG1808
universe u

theorem solution
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 7)
    (hnoRainbow : ¬ HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  exact OPG1808SmallOrders.source_up_to_7 D color htournament horder hnoRainbow
