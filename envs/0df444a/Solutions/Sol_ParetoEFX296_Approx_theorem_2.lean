-- Prove2me | solution 1 for ParetoEFX296.Approx.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:50:04.366599+00:00
-- url     : https://prove2.me/submissions/f9c79afd-b416-4f32-b58c-11efd8a830a0

import Definitions.Def_ParetoEFX296_Approx_Instance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

-- P034Base.lean
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ParetoEFX296.Approx.P034
open ParetoEFX296.Approx

def slope : Agent → Good → Nat
  | .one, .x => 3 | .one, .y => 2
  | .one, .a | .one, .b | .one, .e => 1
  | .two, .x => 2 | .two, .y => 3
  | .two, .b | .two, .c | .two, .e => 1
  | .three, .x => 3 | .three, .y => 2
  | .three, .c | .three, .d | .three, .e => 1
  | .four, .x => 2 | .four, .y => 3
  | .four, .a | .four, .d | .four, .e => 1
  | _, _ => 0

def constant : Agent → Good → Nat
  | .one, .y | .one, .p => 2
  | .one, .c | .one, .d | .one, .q => 1
  | .two, .x | .two, .q => 2
  | .two, .a | .two, .d | .two, .p => 1
  | .three, .y | .three, .p => 2
  | .three, .a | .three, .b | .three, .q => 1
  | .four, .x | .four, .q => 2
  | .four, .b | .four, .c | .four, .p => 1
  | _, _ => 0

def base (i : Agent) (g : Good) : Nat := 6 * slope i g + constant i g

def coeffValue (v : Agent → Good → Nat) (A : Allocation Agent Good)
    (i j : Agent) : Nat :=
  (if A .x = j then v i .x else 0) +
  (if A .y = j then v i .y else 0) +
  (if A .a = j then v i .a else 0) +
  (if A .b = j then v i .b else 0) +
  (if A .c = j then v i .c else 0) +
  (if A .d = j then v i .d else 0) +
  (if A .e = j then v i .e else 0) +
  (if A .p = j then v i .p else 0) +
  (if A .q = j then v i .q else 0)

def obstruct (A : Allocation Agent Good) (i : Agent) (g : Good) : Bool :=
  let j := A g
  let a := coeffValue slope A i i
  let b := coeffValue base A i i
  let c := coeffValue slope A i j - slope i g
  let d := coeffValue base A i j - base i g
  decide (i ≠ j ∧ 0 < d ∧ 3*a ≤ 2*c ∧ 3*b+18*a ≤ 2*d+15*c ∧ 18*b ≤ 15*d)

def agents : List Agent := [.one,.two,.three,.four]
def goods : List Good := [.x,.y,.a,.b,.c,.d,.e,.p,.q]

def obstructed (A : Allocation Agent Good) : Bool :=
  agents.any fun i => goods.any fun g => obstruct A i g

def alloc (x y a b c d e p q : Agent) : Allocation Agent Good
  | .x => x | .y => y | .a => a | .b => b | .c => c | .d => d
  | .e => e | .p => p | .q => q

def dominators : List (Allocation Agent Good) := [
  alloc .one .three .four .two .two .four .two .three .four,
  alloc .one .three .four .two .two .four .four .three .two,
  alloc .four .two .one .one .three .three .one .three .four,
  alloc .four .two .one .one .three .three .three .one .four,
  alloc .three .one .four .two .two .four .two .one .four,
  alloc .three .one .four .two .two .four .four .one .two,
  alloc .two .four .one .one .three .three .one .three .two,
  alloc .two .four .one .one .three .three .three .one .two,
  alloc .one .two .four .two .three .four .three .three .four,
  alloc .one .four .four .two .two .three .three .three .two,
  alloc .one .two .four .one .three .three .four .three .four,
  alloc .three .two .one .one .three .four .four .one .four,
  alloc .three .two .four .one .two .four .one .one .four,
  alloc .three .four .one .two .two .four .one .one .two,
  alloc .one .four .one .two .three .three .two .three .two,
  alloc .three .four .one .one .two .three .two .one .two
]

def dominates (A B : Allocation Agent Good) : Bool :=
  (agents.all fun i => decide (coeffValue slope A i i ≤ coeffValue slope B i i ∧
    coeffValue base A i i ≤ coeffValue base B i i)) &&
  (agents.any fun i => decide (coeffValue base A i i < coeffValue base B i i))

def covered (A : Allocation Agent Good) : Bool :=
  obstructed A || dominators.any (dominates A)


end ParetoEFX296.Approx.P034

-- P034Bridge.lean
set_option autoImplicit false
set_option maxHeartbeats 0
namespace ParetoEFX296.Approx.P034
open ParetoEFX296.Approx

lemma coefficient_identity (K : ℕ) (i : Agent) (g : Good) :
    inst K i g = (slope i g : ℝ) * ((K : ℝ) - 6) + (base i g : ℝ) := by
  cases i <;> cases g <;> norm_num [inst, slope, base, constant] <;> ring

lemma coeffValue_eq_sum (v : Agent → Good → Nat) (A : Allocation Agent Good)
    (i j : Agent) : coeffValue v A i j = ∑ g ∈ bundle A j, v i g := by
  have h : (Finset.univ : Finset Good) = {.x,.y,.a,.b,.c,.d,.e,.p,.q} := rfl
  simp [bundle, Finset.sum_filter, h, coeffValue, add_assoc]

lemma value_identity (K : ℕ) (A : Allocation Agent Good) (i j : Agent) :
    value (inst K) i (bundle A j) =
    (coeffValue slope A i j : ℝ) * ((K : ℝ) - 6) + (coeffValue base A i j : ℝ) := by
  simp only [value, coefficient_identity, Finset.sum_add_distrib,
    ← Finset.sum_mul, coeffValue_eq_sum, Nat.cast_sum]

lemma coeffValue_ge_entry (v : Agent → Good → Nat) (A : Allocation Agent Good)
    (i : Agent) (g : Good) : v i g ≤ coeffValue v A i (A g) := by
  rw [coeffValue_eq_sum]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [bundle])

lemma erased_value_identity (K : ℕ) (A : Allocation Agent Good) (i : Agent) (g : Good) :
    value (inst K) i ((bundle A (A g)).erase g) =
    ((coeffValue slope A i (A g) - slope i g : Nat) : ℝ) * ((K : ℝ) - 6) +
      ((coeffValue base A i (A g) - base i g : Nat) : ℝ) := by
  have hg : g ∈ bundle A (A g) := by simp [bundle]
  have hsum : value (inst K) i ((bundle A (A g)).erase g) + inst K i g =
      value (inst K) i (bundle A (A g)) := by
    exact Finset.sum_erase_add _ _ hg
  rw [value_identity, coefficient_identity] at hsum
  rw [Nat.cast_sub (coeffValue_ge_entry slope A i g),
    Nat.cast_sub (coeffValue_ge_entry base A i g)]
  linarith

lemma obstruction_algebra (K a b c d : Nat) (hK : 6 ≤ K)
    (hd : 0 < d) (h₂ : 3*a ≤ 2*c)
    (h₁ : 3*b + 18*a ≤ 2*d + 15*c) (h₀ : 18*b ≤ 15*d)
    (α : ℝ) (hα : (2 : ℝ)/3 + 1/(K:ℝ) < α) :
    (a:ℝ)*((K:ℝ)-6)+(b:ℝ) < α*((c:ℝ)*((K:ℝ)-6)+(d:ℝ)) := by
  have hKr : (6:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hKpos : (0:ℝ) < (K:ℝ) := by linarith
  have ht : (0:ℝ) ≤ (K:ℝ)-6 := by linarith
  have hdr : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have h₂r : (3:ℝ)*a ≤ 2*c := by exact_mod_cast h₂
  have h₁r : (3:ℝ)*b+18*a ≤ 2*d+15*c := by exact_mod_cast h₁
  have h₀r : (18:ℝ)*b ≤ 15*d := by exact_mod_cast h₀
  have hprod₂ := mul_nonneg (sub_nonneg.mpr h₂r) (sq_nonneg ((K:ℝ)-6))
  have hprod₁ := mul_nonneg (sub_nonneg.mpr h₁r) ht
  have hpoly : (3:ℝ)*K*((a:ℝ)*((K:ℝ)-6)+(b:ℝ)) ≤
      (2*(K:ℝ)+3)*((c:ℝ)*((K:ℝ)-6)+(d:ℝ)) := by
    nlinarith
  have hwpos : (0:ℝ) < (c:ℝ)*((K:ℝ)-6)+(d:ℝ) := by positivity
  have hx : (1:ℝ)/(K:ℝ) < α-2/3 := by linarith
  have hx' := (div_lt_iff₀ hKpos).mp hx
  have halpha : 2*(K:ℝ)+3 < 3*(K:ℝ)*α := by nlinarith
  have hm := mul_lt_mul_of_pos_right halpha hwpos
  nlinarith

lemma obstruct_sound (K : Nat) (hK : 6 ≤ K) (α : ℝ)
    (hα : (2:ℝ)/3+1/(K:ℝ)<α) (A : Allocation Agent Good) (i : Agent) (g : Good)
    (h : obstruct A i g = true) : ¬ IsAlphaEFX (inst K) α A := by
  simp only [obstruct, decide_eq_true_eq] at h
  intro hefx
  have hg : g ∈ bundle A (A g) := by simp [bundle]
  have hle := hefx i (A g) h.1 g hg
  rw [erased_value_identity, value_identity] at hle
  exact (not_lt_of_ge hle) (obstruction_algebra K _ _ _ _ hK h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2 α hα)

lemma dominates_sound (K : Nat) (hK : 6 ≤ K) (A B : Allocation Agent Good)
    (h : dominates A B = true) : ParetoDominates (inst K) B A := by
  have hKr : (6:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have ht : (0:ℝ) ≤ (K:ℝ)-6 := by linarith
  simp only [dominates, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  have hi (i : Agent) : i ∈ agents := by cases i <;> simp [agents]
  constructor
  · intro i
    have hle := h.1 i (hi i)
    rw [value_identity, value_identity]
    have hs : (coeffValue slope A i i : ℝ) ≤ coeffValue slope B i i :=
      by exact_mod_cast hle.1
    have hb : (coeffValue base A i i : ℝ) ≤ coeffValue base B i i :=
      by exact_mod_cast hle.2
    exact add_le_add (mul_le_mul_of_nonneg_right hs ht) hb
  · obtain ⟨i, _, hlt⟩ := h.2
    refine ⟨i, ?_⟩
    rw [value_identity, value_identity]
    have hs : (coeffValue slope A i i : ℝ) ≤ coeffValue slope B i i :=
      by exact_mod_cast (h.1 i (hi i)).1
    have hb : (coeffValue base A i i : ℝ) < coeffValue base B i i :=
      by exact_mod_cast hlt
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right hs ht) hb

lemma covered_sound (K : Nat) (hK : 6 ≤ K) (α : ℝ)
    (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (A : Allocation Agent Good) (h : covered A = true) :
    ¬ (IsAlphaEFX (inst K) α A ∧ IsParetoOptimal (inst K) A) := by
  intro ⟨hefx, hpareto⟩
  simp only [covered, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [obstructed, List.any_eq_true] at h
    obtain ⟨i, _, g, _, hg⟩ := h
    exact obstruct_sound K hK α hα A i g hg hefx
  · simp only [List.any_eq_true] at h
    obtain ⟨B, _, hB⟩ := h
    exact hpareto ⟨B, dominates_sound K hK A B hB⟩

end ParetoEFX296.Approx.P034

-- P034PartialBase.lean
set_option autoImplicit false
namespace ParetoEFX296.Approx.P034

abbrev Partial := Good → Option Agent

def Matches (M : Partial) (A : Allocation Agent Good) : Prop :=
  ∀ g i, M g = some i → A g = i

def fill (M : Partial) (i : Agent) : Allocation Agent Good :=
  fun g => (M g).getD i

def setOwner (M : Partial) (g : Good) (i : Agent) : Partial :=
  fun h => if h = g then some i else M h

def emptyPartial : Partial := fun _ => none

inductive CubeCertificate where
  | efx : Agent → Good → CubeCertificate
  | dom : Allocation Agent Good → CubeCertificate

inductive CubeTree where
  | leaf : CubeCertificate → CubeTree
  | branch : Good → CubeTree → CubeTree → CubeTree → CubeTree → CubeTree

def dominatesPartial (M : Partial) (B : Allocation Agent Good) : Bool :=
  (agents.all fun i => decide (coeffValue slope (fill M i) i i ≤ coeffValue slope B i i ∧
    coeffValue base (fill M i) i i ≤ coeffValue base B i i)) &&
  (agents.any fun i => decide (coeffValue base (fill M i) i i < coeffValue base B i i))

def validLeaf (M : Partial) : CubeCertificate → Bool
  | .efx i g => decide (M g ≠ none) && obstruct (fill M i) i g
  | .dom B => dominatesPartial M B

def validTree (M : Partial) : CubeTree → Bool
  | .leaf c => validLeaf M c
  | .branch g t₁ t₂ t₃ t₄ =>
    validTree (setOwner M g .one) t₁ && validTree (setOwner M g .two) t₂ &&
    validTree (setOwner M g .three) t₃ && validTree (setOwner M g .four) t₄

lemma matches_setOwner (M : Partial) (A : Allocation Agent Good)
    (h : Matches M A) (g : Good) : Matches (setOwner M g (A g)) A := by
  intro k i hi
  by_cases hk : k = g
  · subst k
    simpa [setOwner] using hi
  · exact h k i (by simpa [setOwner, hk] using hi)

lemma matches_empty (A : Allocation Agent Good) : Matches emptyPartial A := by
  intro g i h
  simp [emptyPartial] at h

end ParetoEFX296.Approx.P034

-- P034PartialEFX.lean
set_option autoImplicit false

namespace ParetoEFX296.Approx.P034

/-- Giving every unknown good to i contains any matching allocation's i-bundle. -/
lemma bundle_own_subset_fill (M : Partial) (A : Allocation Agent Good)
    (h : Matches M A) (i : Agent) :
    bundle A i ⊆ bundle (fill M i) i := by
  intro g hg
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  cases hm : M g with
  | none => simp [fill, hm]
  | some j =>
    have hj := h g j hm
    simpa [fill, hm] using hj.symm.trans hg

/-- A different agent's bundle in the completed partial allocation consists
only of fixed goods, hence is contained in every matching allocation. -/
lemma bundle_fill_foreign_subset (M : Partial) (A : Allocation Agent Good)
    (h : Matches M A) (i j : Agent) (hij : i ≠ j) :
    bundle (fill M i) j ⊆ bundle A j := by
  intro g hg
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  cases hm : M g with
  | none =>
    have he : i = j := by simpa [fill, hm] using hg
    exact (hij he).elim
  | some k =>
    have he : k = j := by simpa [fill, hm] using hg
    exact (h g k hm).trans he

lemma coeff_own_le_fill (v : Agent → Good → Nat) (M : Partial)
    (A : Allocation Agent Good) (h : Matches M A) (i : Agent) :
    coeffValue v A i i ≤ coeffValue v (fill M i) i i := by
  rw [coeffValue_eq_sum, coeffValue_eq_sum]
  exact Finset.sum_le_sum_of_subset (bundle_own_subset_fill M A h i)

lemma coeff_fill_foreign_le (v : Agent → Good → Nat) (M : Partial)
    (A : Allocation Agent Good) (h : Matches M A) (i j : Agent) (hij : i ≠ j) :
    coeffValue v (fill M i) i j ≤ coeffValue v A i j := by
  rw [coeffValue_eq_sum, coeffValue_eq_sum]
  exact Finset.sum_le_sum_of_subset (bundle_fill_foreign_subset M A h i j hij)

lemma obstruction_conditions_mono {a b c d a' b' c' d' : Nat}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c' ≤ c) (hd : d' ≤ d)
    (h : 0 < d' ∧ 3 * a' ≤ 2 * c' ∧
      3 * b' + 18 * a' ≤ 2 * d' + 15 * c' ∧ 18 * b' ≤ 15 * d') :
    0 < d ∧ 3 * a ≤ 2 * c ∧
      3 * b + 18 * a ≤ 2 * d + 15 * c ∧ 18 * b ≤ 15 * d := by
  omega

/-- The obstruction inequalities become stronger when the envious agent's
bundle shrinks and the other bundle grows. The removed good has a fixed owner. -/
lemma partial_obstruct_transfer (M : Partial) (A : Allocation Agent Good)
    (h : Matches M A) (i : Agent) (g : Good) (hg : M g ≠ none)
    (ho : obstruct (fill M i) i g = true) : obstruct A i g = true := by
  cases hm : M g with
  | none => simp_all
  | some j =>
    have hAg : A g = j := h g j hm
    have hFg : fill M i g = j := by simp [fill, hm]
    simp only [obstruct, hFg, decide_eq_true_eq] at ho
    have ha := coeff_own_le_fill slope M A h i
    have hb := coeff_own_le_fill base M A h i
    have hc := Nat.sub_le_sub_right (coeff_fill_foreign_le slope M A h i j ho.1)
      (slope i g)
    have hd := Nat.sub_le_sub_right (coeff_fill_foreign_le base M A h i j ho.1)
      (base i g)
    simp only [obstruct, hAg, decide_eq_true_eq]
    exact ⟨ho.1, obstruction_conditions_mono ha hb hc hd ho.2⟩

lemma partial_efx_sound (K : Nat) (hK : 6 ≤ K) (α : ℝ)
    (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (M : Partial) (A : Allocation Agent Good) (h : Matches M A)
    (i : Agent) (g : Good) (hg : M g ≠ none)
    (ho : obstruct (fill M i) i g = true) : ¬ IsAlphaEFX (inst K) α A := by
  exact obstruct_sound K hK α hα A i g (partial_obstruct_transfer M A h i g hg ho)

end ParetoEFX296.Approx.P034

-- P034PartialSound.lean
set_option autoImplicit false
set_option maxHeartbeats 0
namespace ParetoEFX296.Approx.P034

lemma partial_dominates_transfer (M : Partial) (A B : Allocation Agent Good)
    (hm : Matches M A) (h : dominatesPartial M B = true) :
    dominates A B = true := by
  simp only [dominatesPartial, Bool.and_eq_true, List.all_eq_true,
    List.any_eq_true, decide_eq_true_eq] at h
  simp only [dominates, Bool.and_eq_true, List.all_eq_true,
    List.any_eq_true, decide_eq_true_eq]
  constructor
  · intro i hi
    exact ⟨(coeff_own_le_fill slope M A hm i).trans (h.1 i hi).1,
      (coeff_own_le_fill base M A hm i).trans (h.1 i hi).2⟩
  · obtain ⟨i, hi, hlt⟩ := h.2
    exact ⟨i, hi, lt_of_le_of_lt (coeff_own_le_fill base M A hm i) hlt⟩

lemma validTree_sound (K : Nat) (hK : 6 ≤ K) (α : ℝ)
    (hα : (2:ℝ)/3+1/(K:ℝ)<α) (M : Partial) (t : CubeTree)
    (A : Allocation Agent Good) (hm : Matches M A) (hv : validTree M t = true) :
    ¬ (IsAlphaEFX (inst K) α A ∧ IsParetoOptimal (inst K) A) := by
  induction t generalizing M with
  | leaf c =>
    cases c with
    | efx i g =>
      simp only [validTree, validLeaf, Bool.and_eq_true, decide_eq_true_eq] at hv
      intro h
      exact partial_efx_sound K hK α hα M A hm i g hv.1 hv.2 h.1
    | dom B =>
      simp only [validTree, validLeaf] at hv
      intro h
      exact h.2 ⟨B, dominates_sound K hK A B (partial_dominates_transfer M A B hm hv)⟩
  | branch g t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    simp only [validTree, Bool.and_eq_true] at hv
    have hm' := matches_setOwner M A hm g
    cases ha : A g with
    | one => exact ih₁ _ (by simpa [ha] using hm') hv.1.1.1
    | two => exact ih₂ _ (by simpa [ha] using hm') hv.1.1.2
    | three => exact ih₃ _ (by simpa [ha] using hm') hv.1.2
    | four => exact ih₄ _ (by simpa [ha] using hm') hv.2

lemma theorem_from_certificate (t : CubeTree) (hv : validTree emptyPartial t = true)
    (K : ℕ) (hK : 6 ≤ K) :
    (∀ (i : Agent) (g : Good), 0 < inst K i g) ∧
    ∀ α : ℝ, (2 : ℝ) / 3 + 1 / (K : ℝ) < α →
      ¬ ∃ A : Allocation Agent Good,
        IsAlphaEFX (inst K) α A ∧ IsParetoOptimal (inst K) A := by
  have hKr : (6:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hKpos : (0:ℝ) < (K:ℝ) := by linarith
  constructor
  · intro i g
    cases i <;> cases g <;> simp only [inst] <;> positivity
  · intro α hα h
    obtain ⟨A, ha⟩ := h
    exact validTree_sound K hK α hα emptyPartial t A (matches_empty A) hv ha

end ParetoEFX296.Approx.P034

-- P034CubeData.lean
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ParetoEFX296.Approx.P034

-- Externally searched data. The theorem below checks every leaf in the Lean kernel.
def cubeNode0 : CubeTree := .leaf (.efx .two .x)
def cubeNode1 : CubeTree := .leaf (.efx .two .a)
def cubeNode2 : CubeTree := .leaf (.efx .four .x)
def cubeNode3 : CubeTree := .leaf (.efx .three .y)
def cubeNode4 : CubeTree := .leaf (.efx .three .x)
def cubeNode5 : CubeTree := .branch .c cubeNode0 cubeNode4 cubeNode0 cubeNode0
def cubeNode6 : CubeTree := .branch .b cubeNode0 cubeNode3 cubeNode5 cubeNode3
def cubeNode7 : CubeTree := .branch .a cubeNode1 cubeNode2 cubeNode2 cubeNode6
def cubeNode8 : CubeTree := .branch .c cubeNode0 cubeNode3 cubeNode0 cubeNode0
def cubeNode9 : CubeTree := .branch .b cubeNode0 cubeNode8 cubeNode0 cubeNode0
def cubeNode10 : CubeTree := .branch .a cubeNode1 cubeNode2 cubeNode2 cubeNode9
def cubeNode11 : CubeTree := .branch .b cubeNode0 cubeNode3 cubeNode0 cubeNode0
def cubeNode12 : CubeTree := .branch .b cubeNode0 cubeNode5 cubeNode0 cubeNode0
def cubeNode13 : CubeTree := .branch .a cubeNode1 cubeNode11 cubeNode12 cubeNode11
def cubeNode14 : CubeTree := .branch .e cubeNode0 cubeNode7 cubeNode10 cubeNode13
def cubeNode15 : CubeTree := .leaf (.efx .three .a)
def cubeNode16 : CubeTree := .leaf (.efx .four .e)
def cubeNode17 : CubeTree := .leaf (.efx .three .b)
def cubeNode18 : CubeTree := .leaf (.efx .three .e)
def cubeNode19 : CubeTree := .branch .d cubeNode4 cubeNode18 cubeNode16 cubeNode18
def cubeNode20 : CubeTree := .branch .c cubeNode4 cubeNode18 cubeNode19 cubeNode18
def cubeNode21 : CubeTree := .branch .b cubeNode17 cubeNode18 cubeNode20 cubeNode18
def cubeNode22 : CubeTree := .branch .a cubeNode15 cubeNode16 cubeNode16 cubeNode21
def cubeNode23 : CubeTree := .leaf (.efx .four .a)
def cubeNode24 : CubeTree := .leaf (.efx .three .c)
def cubeNode25 : CubeTree := .branch .c cubeNode24 cubeNode3 cubeNode16 cubeNode18
def cubeNode26 : CubeTree := .leaf (.efx .three .d)
def cubeNode27 : CubeTree := .branch .d cubeNode26 cubeNode3 cubeNode16 cubeNode18
def cubeNode28 : CubeTree := .branch .c cubeNode24 cubeNode3 cubeNode27 cubeNode18
def cubeNode29 : CubeTree := .branch .b cubeNode17 cubeNode17 cubeNode25 cubeNode28
def cubeNode30 : CubeTree := .branch .a cubeNode23 cubeNode15 cubeNode16 cubeNode29
def cubeNode31 : CubeTree := .leaf (.efx .four .b)
def cubeNode32 : CubeTree := .leaf (.efx .four .c)
def cubeNode33 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode23 cubeNode17
def cubeNode34 : CubeTree := .branch .c cubeNode32 cubeNode32 cubeNode32 cubeNode33
def cubeNode35 : CubeTree := .branch .b cubeNode31 cubeNode31 cubeNode31 cubeNode34
def cubeNode36 : CubeTree := .branch .d cubeNode17 cubeNode17 cubeNode31 cubeNode17
def cubeNode37 : CubeTree := .branch .c cubeNode17 cubeNode17 cubeNode36 cubeNode17
def cubeNode38 : CubeTree := .branch .d cubeNode26 cubeNode17 cubeNode31 cubeNode17
def cubeNode39 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode31 cubeNode38
def cubeNode40 : CubeTree := .branch .d cubeNode4 cubeNode24 cubeNode32 cubeNode24
def cubeNode41 : CubeTree := .leaf (.efx .four .d)
def cubeNode42 : CubeTree := .leaf (.efx .three .p)
def cubeNode43 : CubeTree := .leaf (.efx .four .p)
def cubeNode44 : CubeTree := .leaf (.efx .three .q)
def cubeNode45 : CubeTree := .leaf (.efx .four .q)
def cubeNode46 : CubeTree := .leaf (.dom (alloc .one .three .four .two .two .four .two .three .four))
def cubeNode47 : CubeTree := .branch .q cubeNode44 cubeNode45 cubeNode46 cubeNode46
def cubeNode48 : CubeTree := .leaf (.dom (alloc .four .two .one .one .three .three .one .three .four))
def cubeNode49 : CubeTree := .branch .q cubeNode44 cubeNode45 cubeNode46 cubeNode48
def cubeNode50 : CubeTree := .branch .p cubeNode42 cubeNode43 cubeNode47 cubeNode49
def cubeNode51 : CubeTree := .branch .d cubeNode41 cubeNode41 cubeNode31 cubeNode50
def cubeNode52 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode31 cubeNode15
def cubeNode53 : CubeTree := .branch .c cubeNode40 cubeNode32 cubeNode51 cubeNode52
def cubeNode54 : CubeTree := .branch .d cubeNode26 cubeNode3 cubeNode32 cubeNode24
def cubeNode55 : CubeTree := .branch .p cubeNode42 cubeNode43 cubeNode49 cubeNode49
def cubeNode56 : CubeTree := .branch .d cubeNode26 cubeNode41 cubeNode32 cubeNode55
def cubeNode57 : CubeTree := .branch .q cubeNode44 cubeNode45 cubeNode45 cubeNode46
def cubeNode58 : CubeTree := .branch .p cubeNode42 cubeNode43 cubeNode43 cubeNode57
def cubeNode59 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode58 cubeNode15
def cubeNode60 : CubeTree := .branch .c cubeNode24 cubeNode54 cubeNode56 cubeNode59
def cubeNode61 : CubeTree := .branch .b cubeNode37 cubeNode39 cubeNode53 cubeNode60
def cubeNode62 : CubeTree := .branch .a cubeNode23 cubeNode23 cubeNode35 cubeNode61
def cubeNode63 : CubeTree := .branch .d cubeNode15 cubeNode15 cubeNode23 cubeNode15
def cubeNode64 : CubeTree := .branch .c cubeNode15 cubeNode15 cubeNode63 cubeNode15
def cubeNode65 : CubeTree := .branch .b cubeNode15 cubeNode15 cubeNode64 cubeNode15
def cubeNode66 : CubeTree := .branch .c cubeNode24 cubeNode15 cubeNode23 cubeNode15
def cubeNode67 : CubeTree := .branch .d cubeNode26 cubeNode15 cubeNode23 cubeNode15
def cubeNode68 : CubeTree := .branch .c cubeNode24 cubeNode15 cubeNode67 cubeNode15
def cubeNode69 : CubeTree := .branch .b cubeNode17 cubeNode31 cubeNode66 cubeNode68
def cubeNode70 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode31 cubeNode17
def cubeNode71 : CubeTree := .branch .q cubeNode44 cubeNode44 cubeNode46 cubeNode44
def cubeNode72 : CubeTree := .branch .p cubeNode42 cubeNode42 cubeNode71 cubeNode42
def cubeNode73 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode31 cubeNode72
def cubeNode74 : CubeTree := .branch .d cubeNode4 cubeNode3 cubeNode31 cubeNode24
def cubeNode75 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode73 cubeNode74
def cubeNode76 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode32 cubeNode17
def cubeNode77 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode76 cubeNode17
def cubeNode78 : CubeTree := .branch .b cubeNode37 cubeNode70 cubeNode75 cubeNode77
def cubeNode79 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode38 cubeNode17
def cubeNode80 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode50 cubeNode15
def cubeNode81 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode80 cubeNode15
def cubeNode82 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode55 cubeNode15
def cubeNode83 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode82 cubeNode15
def cubeNode84 : CubeTree := .branch .b cubeNode17 cubeNode79 cubeNode81 cubeNode83
def cubeNode85 : CubeTree := .branch .a cubeNode65 cubeNode69 cubeNode78 cubeNode84
def cubeNode86 : CubeTree := .branch .e cubeNode22 cubeNode30 cubeNode62 cubeNode85
def cubeNode87 : CubeTree := .leaf (.efx .two .d)
def cubeNode88 : CubeTree := .leaf (.efx .two .p)
def cubeNode89 : CubeTree := .branch .p cubeNode88 cubeNode18 cubeNode88 cubeNode18
def cubeNode90 : CubeTree := .branch .d cubeNode87 cubeNode16 cubeNode87 cubeNode89
def cubeNode91 : CubeTree := .leaf (.efx .two .e)
def cubeNode92 : CubeTree := .branch .c cubeNode0 cubeNode90 cubeNode91 cubeNode91
def cubeNode93 : CubeTree := .branch .b cubeNode0 cubeNode92 cubeNode91 cubeNode91
def cubeNode94 : CubeTree := .branch .a cubeNode1 cubeNode16 cubeNode16 cubeNode93
def cubeNode95 : CubeTree := .leaf (.efx .two .c)
def cubeNode96 : CubeTree := .branch .d cubeNode87 cubeNode23 cubeNode87 cubeNode87
def cubeNode97 : CubeTree := .branch .c cubeNode95 cubeNode32 cubeNode95 cubeNode96
def cubeNode98 : CubeTree := .branch .b cubeNode31 cubeNode31 cubeNode31 cubeNode97
def cubeNode99 : CubeTree := .branch .p cubeNode88 cubeNode17 cubeNode88 cubeNode17
def cubeNode100 : CubeTree := .branch .d cubeNode87 cubeNode31 cubeNode87 cubeNode99
def cubeNode101 : CubeTree := .leaf (.efx .two .b)
def cubeNode102 : CubeTree := .branch .c cubeNode0 cubeNode100 cubeNode101 cubeNode101
def cubeNode103 : CubeTree := .branch .p cubeNode88 cubeNode24 cubeNode88 cubeNode24
def cubeNode104 : CubeTree := .branch .d cubeNode87 cubeNode32 cubeNode87 cubeNode103
def cubeNode105 : CubeTree := .leaf (.dom (alloc .one .two .four .two .three .four .three .three .four))
def cubeNode106 : CubeTree := .branch .q cubeNode44 cubeNode105 cubeNode45 cubeNode105
def cubeNode107 : CubeTree := .branch .q cubeNode44 cubeNode105 cubeNode45 cubeNode48
def cubeNode108 : CubeTree := .branch .p cubeNode42 cubeNode106 cubeNode43 cubeNode107
def cubeNode109 : CubeTree := .branch .d cubeNode41 cubeNode31 cubeNode41 cubeNode108
def cubeNode110 : CubeTree := .leaf (.efx .two .q)
def cubeNode111 : CubeTree := .leaf (.dom (alloc .one .three .four .two .two .four .four .three .two))
def cubeNode112 : CubeTree := .branch .q cubeNode44 cubeNode46 cubeNode110 cubeNode111
def cubeNode113 : CubeTree := .branch .p cubeNode42 cubeNode112 cubeNode88 cubeNode112
def cubeNode114 : CubeTree := .branch .d cubeNode41 cubeNode31 cubeNode87 cubeNode113
def cubeNode115 : CubeTree := .branch .c cubeNode104 cubeNode109 cubeNode32 cubeNode114
def cubeNode116 : CubeTree := .leaf (.efx .two .y)
def cubeNode117 : CubeTree := .branch .c cubeNode95 cubeNode31 cubeNode116 cubeNode101
def cubeNode118 : CubeTree := .branch .d cubeNode41 cubeNode32 cubeNode87 cubeNode113
def cubeNode119 : CubeTree := .branch .c cubeNode95 cubeNode118 cubeNode95 cubeNode1
def cubeNode120 : CubeTree := .branch .b cubeNode102 cubeNode115 cubeNode117 cubeNode119
def cubeNode121 : CubeTree := .branch .a cubeNode23 cubeNode98 cubeNode23 cubeNode120
def cubeNode122 : CubeTree := .branch .c cubeNode95 cubeNode16 cubeNode116 cubeNode91
def cubeNode123 : CubeTree := .branch .b cubeNode101 cubeNode122 cubeNode116 cubeNode91
def cubeNode124 : CubeTree := .branch .a cubeNode23 cubeNode16 cubeNode1 cubeNode123
def cubeNode125 : CubeTree := .branch .p cubeNode15 cubeNode15 cubeNode88 cubeNode15
def cubeNode126 : CubeTree := .branch .d cubeNode15 cubeNode23 cubeNode87 cubeNode125
def cubeNode127 : CubeTree := .branch .c cubeNode1 cubeNode126 cubeNode1 cubeNode1
def cubeNode128 : CubeTree := .branch .b cubeNode1 cubeNode127 cubeNode1 cubeNode1
def cubeNode129 : CubeTree := .branch .q cubeNode44 cubeNode46 cubeNode110 cubeNode46
def cubeNode130 : CubeTree := .branch .p cubeNode42 cubeNode129 cubeNode88 cubeNode112
def cubeNode131 : CubeTree := .branch .d cubeNode41 cubeNode31 cubeNode41 cubeNode130
def cubeNode132 : CubeTree := .branch .d cubeNode87 cubeNode31 cubeNode87 cubeNode87
def cubeNode133 : CubeTree := .branch .c cubeNode95 cubeNode131 cubeNode95 cubeNode132
def cubeNode134 : CubeTree := .branch .d cubeNode87 cubeNode32 cubeNode87 cubeNode87
def cubeNode135 : CubeTree := .branch .c cubeNode0 cubeNode134 cubeNode116 cubeNode101
def cubeNode136 : CubeTree := .branch .b cubeNode101 cubeNode133 cubeNode101 cubeNode135
def cubeNode137 : CubeTree := .branch .c cubeNode95 cubeNode23 cubeNode1 cubeNode1
def cubeNode138 : CubeTree := .branch .b cubeNode101 cubeNode137 cubeNode1 cubeNode1
def cubeNode139 : CubeTree := .branch .p cubeNode26 cubeNode26 cubeNode88 cubeNode26
def cubeNode140 : CubeTree := .leaf (.dom (alloc .two .four .one .one .three .three .one .three .two))
def cubeNode141 : CubeTree := .leaf (.dom (alloc .one .four .four .two .two .three .three .three .two))
def cubeNode142 : CubeTree := .branch .q cubeNode44 cubeNode140 cubeNode110 cubeNode141
def cubeNode143 : CubeTree := .branch .q cubeNode44 cubeNode141 cubeNode110 cubeNode141
def cubeNode144 : CubeTree := .branch .p cubeNode42 cubeNode142 cubeNode88 cubeNode143
def cubeNode145 : CubeTree := .branch .d cubeNode139 cubeNode130 cubeNode87 cubeNode144
def cubeNode146 : CubeTree := .branch .c cubeNode95 cubeNode145 cubeNode95 cubeNode1
def cubeNode147 : CubeTree := .branch .b cubeNode101 cubeNode146 cubeNode101 cubeNode1
def cubeNode148 : CubeTree := .branch .a cubeNode128 cubeNode136 cubeNode138 cubeNode147
def cubeNode149 : CubeTree := .branch .e cubeNode94 cubeNode121 cubeNode124 cubeNode148
def cubeNode150 : CubeTree := .branch .b cubeNode101 cubeNode18 cubeNode91 cubeNode91
def cubeNode151 : CubeTree := .branch .c cubeNode0 cubeNode18 cubeNode91 cubeNode91
def cubeNode152 : CubeTree := .branch .b cubeNode0 cubeNode151 cubeNode91 cubeNode91
def cubeNode153 : CubeTree := .branch .b cubeNode0 cubeNode18 cubeNode91 cubeNode91
def cubeNode154 : CubeTree := .branch .a cubeNode1 cubeNode150 cubeNode152 cubeNode153
def cubeNode155 : CubeTree := .branch .c cubeNode1 cubeNode15 cubeNode1 cubeNode1
def cubeNode156 : CubeTree := .branch .b cubeNode1 cubeNode15 cubeNode155 cubeNode15
def cubeNode157 : CubeTree := .branch .q cubeNode44 cubeNode140 cubeNode111 cubeNode110
def cubeNode158 : CubeTree := .branch .p cubeNode42 cubeNode157 cubeNode157 cubeNode88
def cubeNode159 : CubeTree := .branch .d cubeNode26 cubeNode15 cubeNode158 cubeNode26
def cubeNode160 : CubeTree := .branch .c cubeNode24 cubeNode15 cubeNode159 cubeNode24
def cubeNode161 : CubeTree := .branch .d cubeNode87 cubeNode15 cubeNode87 cubeNode87
def cubeNode162 : CubeTree := .branch .c cubeNode95 cubeNode15 cubeNode161 cubeNode95
def cubeNode163 : CubeTree := .branch .c cubeNode95 cubeNode15 cubeNode101 cubeNode101
def cubeNode164 : CubeTree := .branch .b cubeNode17 cubeNode160 cubeNode162 cubeNode163
def cubeNode165 : CubeTree := .branch .c cubeNode0 cubeNode17 cubeNode101 cubeNode101
def cubeNode166 : CubeTree := .branch .q cubeNode44 cubeNode111 cubeNode111 cubeNode110
def cubeNode167 : CubeTree := .branch .p cubeNode42 cubeNode157 cubeNode166 cubeNode88
def cubeNode168 : CubeTree := .branch .d cubeNode26 cubeNode17 cubeNode167 cubeNode87
def cubeNode169 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode168 cubeNode24
def cubeNode170 : CubeTree := .branch .q cubeNode44 cubeNode44 cubeNode111 cubeNode110
def cubeNode171 : CubeTree := .branch .p cubeNode42 cubeNode42 cubeNode170 cubeNode88
def cubeNode172 : CubeTree := .branch .d cubeNode4 cubeNode24 cubeNode171 cubeNode87
def cubeNode173 : CubeTree := .branch .c cubeNode95 cubeNode172 cubeNode1 cubeNode95
def cubeNode174 : CubeTree := .branch .c cubeNode95 cubeNode17 cubeNode101 cubeNode116
def cubeNode175 : CubeTree := .branch .b cubeNode165 cubeNode169 cubeNode173 cubeNode174
def cubeNode176 : CubeTree := .branch .d cubeNode1 cubeNode17 cubeNode1 cubeNode1
def cubeNode177 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode176 cubeNode1
def cubeNode178 : CubeTree := .branch .c cubeNode95 cubeNode15 cubeNode1 cubeNode1
def cubeNode179 : CubeTree := .branch .b cubeNode17 cubeNode177 cubeNode178 cubeNode1
def cubeNode180 : CubeTree := .branch .a cubeNode156 cubeNode164 cubeNode175 cubeNode179
def cubeNode181 : CubeTree := .branch .b cubeNode1 cubeNode155 cubeNode1 cubeNode1
def cubeNode182 : CubeTree := .branch .q cubeNode110 cubeNode111 cubeNode110 cubeNode110
def cubeNode183 : CubeTree := .branch .p cubeNode88 cubeNode182 cubeNode88 cubeNode88
def cubeNode184 : CubeTree := .branch .d cubeNode87 cubeNode183 cubeNode87 cubeNode87
def cubeNode185 : CubeTree := .branch .c cubeNode95 cubeNode159 cubeNode184 cubeNode95
def cubeNode186 : CubeTree := .branch .c cubeNode0 cubeNode161 cubeNode101 cubeNode101
def cubeNode187 : CubeTree := .branch .b cubeNode101 cubeNode185 cubeNode186 cubeNode101
def cubeNode188 : CubeTree := .branch .c cubeNode95 cubeNode168 cubeNode1 cubeNode95
def cubeNode189 : CubeTree := .branch .b cubeNode101 cubeNode188 cubeNode1 cubeNode101
def cubeNode190 : CubeTree := .branch .c cubeNode95 cubeNode176 cubeNode1 cubeNode1
def cubeNode191 : CubeTree := .branch .b cubeNode101 cubeNode190 cubeNode1 cubeNode1
def cubeNode192 : CubeTree := .branch .a cubeNode181 cubeNode187 cubeNode189 cubeNode191
def cubeNode193 : CubeTree := .branch .b cubeNode1 cubeNode15 cubeNode1 cubeNode1
def cubeNode194 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode91 cubeNode95
def cubeNode195 : CubeTree := .branch .b cubeNode101 cubeNode194 cubeNode91 cubeNode101
def cubeNode196 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode91 cubeNode116
def cubeNode197 : CubeTree := .branch .b cubeNode101 cubeNode196 cubeNode91 cubeNode116
def cubeNode198 : CubeTree := .branch .a cubeNode193 cubeNode195 cubeNode197 cubeNode1
def cubeNode199 : CubeTree := .branch .e cubeNode154 cubeNode180 cubeNode192 cubeNode198
def cubeNode200 : CubeTree := .branch .y cubeNode14 cubeNode86 cubeNode149 cubeNode199
def cubeNode201 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode16 cubeNode18
def cubeNode202 : CubeTree := .branch .d cubeNode87 cubeNode18 cubeNode16 cubeNode18
def cubeNode203 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode202 cubeNode18
def cubeNode204 : CubeTree := .branch .b cubeNode17 cubeNode17 cubeNode201 cubeNode203
def cubeNode205 : CubeTree := .branch .a cubeNode15 cubeNode16 cubeNode16 cubeNode204
def cubeNode206 : CubeTree := .leaf (.efx .one .b)
def cubeNode207 : CubeTree := .leaf (.efx .one .c)
def cubeNode208 : CubeTree := .leaf (.efx .one .d)
def cubeNode209 : CubeTree := .branch .d cubeNode26 cubeNode208 cubeNode16 cubeNode18
def cubeNode210 : CubeTree := .branch .c cubeNode24 cubeNode207 cubeNode209 cubeNode18
def cubeNode211 : CubeTree := .branch .b cubeNode18 cubeNode206 cubeNode210 cubeNode18
def cubeNode212 : CubeTree := .branch .a cubeNode23 cubeNode15 cubeNode16 cubeNode211
def cubeNode213 : CubeTree := .branch .c cubeNode32 cubeNode32 cubeNode32 cubeNode46
def cubeNode214 : CubeTree := .branch .b cubeNode31 cubeNode31 cubeNode31 cubeNode213
def cubeNode215 : CubeTree := .branch .d cubeNode87 cubeNode17 cubeNode31 cubeNode17
def cubeNode216 : CubeTree := .branch .c cubeNode101 cubeNode24 cubeNode31 cubeNode215
def cubeNode217 : CubeTree := .branch .d cubeNode17 cubeNode208 cubeNode31 cubeNode17
def cubeNode218 : CubeTree := .branch .c cubeNode17 cubeNode207 cubeNode217 cubeNode17
def cubeNode219 : CubeTree := .branch .d cubeNode26 cubeNode4 cubeNode32 cubeNode24
def cubeNode220 : CubeTree := .leaf (.efx .one .p)
def cubeNode221 : CubeTree := .branch .p cubeNode43 cubeNode220 cubeNode46 cubeNode48
def cubeNode222 : CubeTree := .branch .d cubeNode41 cubeNode41 cubeNode31 cubeNode221
def cubeNode223 : CubeTree := .branch .c cubeNode32 cubeNode219 cubeNode222 cubeNode52
def cubeNode224 : CubeTree := .branch .d cubeNode87 cubeNode24 cubeNode32 cubeNode24
def cubeNode225 : CubeTree := .leaf (.efx .one .q)
def cubeNode226 : CubeTree := .branch .q cubeNode110 cubeNode225 cubeNode46 cubeNode111
def cubeNode227 : CubeTree := .branch .p cubeNode43 cubeNode220 cubeNode226 cubeNode48
def cubeNode228 : CubeTree := .branch .d cubeNode41 cubeNode26 cubeNode32 cubeNode227
def cubeNode229 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode46 cubeNode15
def cubeNode230 : CubeTree := .branch .c cubeNode224 cubeNode24 cubeNode228 cubeNode229
def cubeNode231 : CubeTree := .branch .b cubeNode216 cubeNode218 cubeNode223 cubeNode230
def cubeNode232 : CubeTree := .branch .a cubeNode23 cubeNode23 cubeNode214 cubeNode231
def cubeNode233 : CubeTree := .branch .c cubeNode1 cubeNode15 cubeNode23 cubeNode15
def cubeNode234 : CubeTree := .branch .c cubeNode1 cubeNode15 cubeNode63 cubeNode15
def cubeNode235 : CubeTree := .branch .b cubeNode31 cubeNode17 cubeNode233 cubeNode234
def cubeNode236 : CubeTree := .leaf (.efx .one .a)
def cubeNode237 : CubeTree := .branch .d cubeNode26 cubeNode208 cubeNode23 cubeNode15
def cubeNode238 : CubeTree := .branch .c cubeNode24 cubeNode207 cubeNode237 cubeNode15
def cubeNode239 : CubeTree := .branch .b cubeNode15 cubeNode236 cubeNode238 cubeNode15
def cubeNode240 : CubeTree := .branch .c cubeNode101 cubeNode17 cubeNode31 cubeNode17
def cubeNode241 : CubeTree := .branch .d cubeNode26 cubeNode208 cubeNode31 cubeNode17
def cubeNode242 : CubeTree := .branch .c cubeNode24 cubeNode207 cubeNode241 cubeNode17
def cubeNode243 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode31 cubeNode48
def cubeNode244 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode243 cubeNode48
def cubeNode245 : CubeTree := .branch .b cubeNode240 cubeNode242 cubeNode244 cubeNode77
def cubeNode246 : CubeTree := .branch .c cubeNode101 cubeNode17 cubeNode215 cubeNode17
def cubeNode247 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode221 cubeNode15
def cubeNode248 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode247 cubeNode15
def cubeNode249 : CubeTree := .branch .q cubeNode110 cubeNode225 cubeNode46 cubeNode225
def cubeNode250 : CubeTree := .branch .p cubeNode43 cubeNode220 cubeNode249 cubeNode220
def cubeNode251 : CubeTree := .branch .d cubeNode26 cubeNode26 cubeNode250 cubeNode15
def cubeNode252 : CubeTree := .branch .c cubeNode24 cubeNode24 cubeNode251 cubeNode15
def cubeNode253 : CubeTree := .branch .b cubeNode246 cubeNode17 cubeNode248 cubeNode252
def cubeNode254 : CubeTree := .branch .a cubeNode235 cubeNode239 cubeNode245 cubeNode253
def cubeNode255 : CubeTree := .branch .e cubeNode205 cubeNode212 cubeNode232 cubeNode254
def cubeNode256 : CubeTree := .leaf (.efx .one .y)
def cubeNode257 : CubeTree := .leaf (.efx .one .x)
def cubeNode258 : CubeTree := .branch .b cubeNode3 cubeNode257 cubeNode257 cubeNode257
def cubeNode259 : CubeTree := .branch .a cubeNode2 cubeNode256 cubeNode2 cubeNode258
def cubeNode260 : CubeTree := .branch .a cubeNode2 cubeNode257 cubeNode257 cubeNode257
def cubeNode261 : CubeTree := .branch .a cubeNode258 cubeNode257 cubeNode257 cubeNode257
def cubeNode262 : CubeTree := .branch .e cubeNode259 cubeNode256 cubeNode260 cubeNode261
def cubeNode263 : CubeTree := .leaf (.dom (alloc .three .one .four .two .two .four .two .one .four))
def cubeNode264 : CubeTree := .branch .d cubeNode23 cubeNode208 cubeNode23 cubeNode263
def cubeNode265 : CubeTree := .branch .c cubeNode32 cubeNode32 cubeNode32 cubeNode264
def cubeNode266 : CubeTree := .branch .b cubeNode31 cubeNode31 cubeNode31 cubeNode265
def cubeNode267 : CubeTree := .leaf (.dom (alloc .four .two .one .one .three .three .three .one .four))
def cubeNode268 : CubeTree := .branch .p cubeNode46 cubeNode220 cubeNode43 cubeNode267
def cubeNode269 : CubeTree := .branch .d cubeNode31 cubeNode41 cubeNode41 cubeNode268
def cubeNode270 : CubeTree := .branch .d cubeNode31 cubeNode207 cubeNode207 cubeNode207
def cubeNode271 : CubeTree := .branch .q cubeNode46 cubeNode225 cubeNode110 cubeNode111
def cubeNode272 : CubeTree := .branch .p cubeNode271 cubeNode220 cubeNode43 cubeNode267
def cubeNode273 : CubeTree := .branch .d cubeNode31 cubeNode208 cubeNode41 cubeNode272
def cubeNode274 : CubeTree := .branch .c cubeNode269 cubeNode270 cubeNode32 cubeNode273
def cubeNode275 : CubeTree := .branch .d cubeNode32 cubeNode208 cubeNode208 cubeNode208
def cubeNode276 : CubeTree := .branch .c cubeNode275 cubeNode207 cubeNode207 cubeNode207
def cubeNode277 : CubeTree := .branch .b cubeNode274 cubeNode206 cubeNode206 cubeNode276
def cubeNode278 : CubeTree := .branch .a cubeNode266 cubeNode23 cubeNode23 cubeNode277
def cubeNode279 : CubeTree := .leaf (.efx .one .e)
def cubeNode280 : CubeTree := .branch .a cubeNode16 cubeNode236 cubeNode279 cubeNode279
def cubeNode281 : CubeTree := .branch .a cubeNode16 cubeNode236 cubeNode236 cubeNode279
def cubeNode282 : CubeTree := .branch .q cubeNode46 cubeNode225 cubeNode110 cubeNode44
def cubeNode283 : CubeTree := .branch .p cubeNode282 cubeNode220 cubeNode43 cubeNode42
def cubeNode284 : CubeTree := .branch .d cubeNode31 cubeNode208 cubeNode41 cubeNode283
def cubeNode285 : CubeTree := .branch .c cubeNode269 cubeNode270 cubeNode32 cubeNode284
def cubeNode286 : CubeTree := .branch .b cubeNode285 cubeNode206 cubeNode206 cubeNode276
def cubeNode287 : CubeTree := .branch .d cubeNode267 cubeNode208 cubeNode208 cubeNode208
def cubeNode288 : CubeTree := .branch .c cubeNode287 cubeNode207 cubeNode207 cubeNode207
def cubeNode289 : CubeTree := .branch .b cubeNode288 cubeNode257 cubeNode256 cubeNode236
def cubeNode290 : CubeTree := .branch .a cubeNode286 cubeNode236 cubeNode236 cubeNode289
def cubeNode291 : CubeTree := .branch .e cubeNode278 cubeNode280 cubeNode281 cubeNode290
def cubeNode292 : CubeTree := .leaf (.dom (alloc .one .four .one .two .three .three .two .three .two))
def cubeNode293 : CubeTree := .branch .q cubeNode292 cubeNode44 cubeNode292 cubeNode110
def cubeNode294 : CubeTree := .branch .q cubeNode292 cubeNode44 cubeNode111 cubeNode110
def cubeNode295 : CubeTree := .branch .q cubeNode88 cubeNode44 cubeNode88 cubeNode88
def cubeNode296 : CubeTree := .branch .p cubeNode293 cubeNode42 cubeNode294 cubeNode295
def cubeNode297 : CubeTree := .branch .d cubeNode15 cubeNode26 cubeNode296 cubeNode26
def cubeNode298 : CubeTree := .branch .c cubeNode15 cubeNode24 cubeNode297 cubeNode24
def cubeNode299 : CubeTree := .branch .q cubeNode111 cubeNode225 cubeNode111 cubeNode110
def cubeNode300 : CubeTree := .branch .q cubeNode88 cubeNode225 cubeNode88 cubeNode88
def cubeNode301 : CubeTree := .branch .p cubeNode299 cubeNode220 cubeNode299 cubeNode300
def cubeNode302 : CubeTree := .branch .d cubeNode15 cubeNode208 cubeNode301 cubeNode26
def cubeNode303 : CubeTree := .branch .c cubeNode15 cubeNode24 cubeNode302 cubeNode24
def cubeNode304 : CubeTree := .branch .q cubeNode101 cubeNode225 cubeNode101 cubeNode225
def cubeNode305 : CubeTree := .branch .p cubeNode304 cubeNode220 cubeNode304 cubeNode220
def cubeNode306 : CubeTree := .branch .d cubeNode15 cubeNode208 cubeNode305 cubeNode208
def cubeNode307 : CubeTree := .branch .c cubeNode15 cubeNode24 cubeNode306 cubeNode207
def cubeNode308 : CubeTree := .branch .b cubeNode298 cubeNode17 cubeNode303 cubeNode307
def cubeNode309 : CubeTree := .branch .b cubeNode15 cubeNode236 cubeNode236 cubeNode236
def cubeNode310 : CubeTree := .branch .d cubeNode17 cubeNode208 cubeNode301 cubeNode26
def cubeNode311 : CubeTree := .branch .c cubeNode17 cubeNode24 cubeNode310 cubeNode24
def cubeNode312 : CubeTree := .branch .d cubeNode24 cubeNode208 cubeNode208 cubeNode208
def cubeNode313 : CubeTree := .branch .c cubeNode312 cubeNode207 cubeNode207 cubeNode207
def cubeNode314 : CubeTree := .branch .b cubeNode311 cubeNode206 cubeNode313 cubeNode206
def cubeNode315 : CubeTree := .branch .q cubeNode1 cubeNode225 cubeNode1 cubeNode225
def cubeNode316 : CubeTree := .branch .p cubeNode315 cubeNode220 cubeNode315 cubeNode220
def cubeNode317 : CubeTree := .branch .d cubeNode17 cubeNode208 cubeNode316 cubeNode208
def cubeNode318 : CubeTree := .branch .c cubeNode17 cubeNode24 cubeNode317 cubeNode207
def cubeNode319 : CubeTree := .branch .b cubeNode318 cubeNode206 cubeNode236 cubeNode236
def cubeNode320 : CubeTree := .branch .a cubeNode308 cubeNode309 cubeNode314 cubeNode319
def cubeNode321 : CubeTree := .branch .b cubeNode18 cubeNode206 cubeNode279 cubeNode279
def cubeNode322 : CubeTree := .branch .a cubeNode321 cubeNode236 cubeNode279 cubeNode279
def cubeNode323 : CubeTree := .branch .d cubeNode15 cubeNode26 cubeNode301 cubeNode26
def cubeNode324 : CubeTree := .leaf (.dom (alloc .three .one .four .two .two .four .four .one .two))
def cubeNode325 : CubeTree := .leaf (.dom (alloc .three .four .one .one .two .three .two .one .two))
def cubeNode326 : CubeTree := .branch .q cubeNode324 cubeNode225 cubeNode325 cubeNode110
def cubeNode327 : CubeTree := .branch .q cubeNode325 cubeNode225 cubeNode325 cubeNode110
def cubeNode328 : CubeTree := .branch .p cubeNode326 cubeNode220 cubeNode327 cubeNode300
def cubeNode329 : CubeTree := .branch .q cubeNode87 cubeNode225 cubeNode87 cubeNode87
def cubeNode330 : CubeTree := .branch .p cubeNode329 cubeNode220 cubeNode329 cubeNode42
def cubeNode331 : CubeTree := .branch .d cubeNode301 cubeNode208 cubeNode328 cubeNode330
def cubeNode332 : CubeTree := .branch .q cubeNode95 cubeNode225 cubeNode95 cubeNode95
def cubeNode333 : CubeTree := .branch .p cubeNode332 cubeNode220 cubeNode332 cubeNode88
def cubeNode334 : CubeTree := .branch .d cubeNode24 cubeNode208 cubeNode333 cubeNode87
def cubeNode335 : CubeTree := .branch .c cubeNode323 cubeNode24 cubeNode331 cubeNode334
def cubeNode336 : CubeTree := .branch .d cubeNode15 cubeNode208 cubeNode208 cubeNode208
def cubeNode337 : CubeTree := .branch .c cubeNode336 cubeNode207 cubeNode207 cubeNode207
def cubeNode338 : CubeTree := .branch .b cubeNode335 cubeNode206 cubeNode337 cubeNode206
def cubeNode339 : CubeTree := .branch .d cubeNode17 cubeNode208 cubeNode208 cubeNode208
def cubeNode340 : CubeTree := .branch .c cubeNode339 cubeNode207 cubeNode207 cubeNode207
def cubeNode341 : CubeTree := .branch .b cubeNode340 cubeNode257 cubeNode236 cubeNode236
def cubeNode342 : CubeTree := .branch .a cubeNode338 cubeNode236 cubeNode341 cubeNode236
def cubeNode343 : CubeTree := .branch .q cubeNode91 cubeNode225 cubeNode91 cubeNode225
def cubeNode344 : CubeTree := .branch .p cubeNode343 cubeNode220 cubeNode343 cubeNode220
def cubeNode345 : CubeTree := .branch .d cubeNode18 cubeNode208 cubeNode344 cubeNode208
def cubeNode346 : CubeTree := .branch .c cubeNode18 cubeNode24 cubeNode345 cubeNode207
def cubeNode347 : CubeTree := .branch .b cubeNode346 cubeNode206 cubeNode279 cubeNode206
def cubeNode348 : CubeTree := .branch .a cubeNode347 cubeNode236 cubeNode279 cubeNode236
def cubeNode349 : CubeTree := .branch .e cubeNode320 cubeNode322 cubeNode342 cubeNode348
def cubeNode350 : CubeTree := .branch .y cubeNode255 cubeNode262 cubeNode291 cubeNode349
def cubeNode351 : CubeTree := .branch .c cubeNode116 cubeNode16 cubeNode91 cubeNode91
def cubeNode352 : CubeTree := .branch .b cubeNode116 cubeNode351 cubeNode91 cubeNode91
def cubeNode353 : CubeTree := .branch .a cubeNode1 cubeNode16 cubeNode16 cubeNode352
def cubeNode354 : CubeTree := .branch .c cubeNode116 cubeNode31 cubeNode101 cubeNode101
def cubeNode355 : CubeTree := .leaf (.dom (alloc .three .two .four .one .two .four .one .one .four))
def cubeNode356 : CubeTree := .branch .q cubeNode45 cubeNode355 cubeNode225 cubeNode355
def cubeNode357 : CubeTree := .branch .q cubeNode45 cubeNode355 cubeNode225 cubeNode267
def cubeNode358 : CubeTree := .branch .p cubeNode43 cubeNode356 cubeNode220 cubeNode357
def cubeNode359 : CubeTree := .branch .d cubeNode41 cubeNode31 cubeNode41 cubeNode358
def cubeNode360 : CubeTree := .branch .p cubeNode88 cubeNode207 cubeNode207 cubeNode207
def cubeNode361 : CubeTree := .branch .d cubeNode87 cubeNode31 cubeNode87 cubeNode360
def cubeNode362 : CubeTree := .branch .q cubeNode110 cubeNode267 cubeNode225 cubeNode267
def cubeNode363 : CubeTree := .branch .p cubeNode88 cubeNode362 cubeNode220 cubeNode362
def cubeNode364 : CubeTree := .branch .d cubeNode87 cubeNode31 cubeNode41 cubeNode363
def cubeNode365 : CubeTree := .branch .c cubeNode32 cubeNode359 cubeNode361 cubeNode364
def cubeNode366 : CubeTree := .branch .p cubeNode88 cubeNode206 cubeNode206 cubeNode206
def cubeNode367 : CubeTree := .branch .d cubeNode87 cubeNode32 cubeNode208 cubeNode366
def cubeNode368 : CubeTree := .branch .c cubeNode95 cubeNode367 cubeNode207 cubeNode101
def cubeNode369 : CubeTree := .branch .d cubeNode87 cubeNode32 cubeNode41 cubeNode363
def cubeNode370 : CubeTree := .branch .c cubeNode95 cubeNode369 cubeNode95 cubeNode1
def cubeNode371 : CubeTree := .branch .b cubeNode354 cubeNode365 cubeNode368 cubeNode370
def cubeNode372 : CubeTree := .branch .a cubeNode23 cubeNode98 cubeNode23 cubeNode371
def cubeNode373 : CubeTree := .branch .p cubeNode88 cubeNode279 cubeNode279 cubeNode279
def cubeNode374 : CubeTree := .branch .d cubeNode87 cubeNode16 cubeNode208 cubeNode373
def cubeNode375 : CubeTree := .branch .c cubeNode95 cubeNode374 cubeNode207 cubeNode91
def cubeNode376 : CubeTree := .branch .b cubeNode101 cubeNode375 cubeNode206 cubeNode91
def cubeNode377 : CubeTree := .branch .a cubeNode23 cubeNode16 cubeNode1 cubeNode376
def cubeNode378 : CubeTree := .branch .c cubeNode1 cubeNode23 cubeNode1 cubeNode1
def cubeNode379 : CubeTree := .branch .b cubeNode1 cubeNode378 cubeNode1 cubeNode1
def cubeNode380 : CubeTree := .branch .d cubeNode41 cubeNode31 cubeNode41 cubeNode363
def cubeNode381 : CubeTree := .branch .c cubeNode95 cubeNode380 cubeNode95 cubeNode132
def cubeNode382 : CubeTree := .branch .c cubeNode116 cubeNode134 cubeNode0 cubeNode101
def cubeNode383 : CubeTree := .branch .b cubeNode101 cubeNode381 cubeNode101 cubeNode382
def cubeNode384 : CubeTree := .branch .p cubeNode88 cubeNode236 cubeNode236 cubeNode236
def cubeNode385 : CubeTree := .branch .d cubeNode87 cubeNode23 cubeNode208 cubeNode384
def cubeNode386 : CubeTree := .branch .c cubeNode95 cubeNode385 cubeNode207 cubeNode1
def cubeNode387 : CubeTree := .branch .b cubeNode101 cubeNode386 cubeNode236 cubeNode1
def cubeNode388 : CubeTree := .branch .p cubeNode88 cubeNode208 cubeNode208 cubeNode208
def cubeNode389 : CubeTree := .leaf (.dom (alloc .two .four .one .one .three .three .three .one .two))
def cubeNode390 : CubeTree := .leaf (.dom (alloc .three .four .one .two .two .four .one .one .two))
def cubeNode391 : CubeTree := .branch .q cubeNode110 cubeNode389 cubeNode225 cubeNode390
def cubeNode392 : CubeTree := .branch .q cubeNode110 cubeNode390 cubeNode225 cubeNode390
def cubeNode393 : CubeTree := .branch .p cubeNode88 cubeNode391 cubeNode220 cubeNode392
def cubeNode394 : CubeTree := .branch .d cubeNode87 cubeNode363 cubeNode388 cubeNode393
def cubeNode395 : CubeTree := .branch .c cubeNode95 cubeNode394 cubeNode95 cubeNode1
def cubeNode396 : CubeTree := .branch .b cubeNode101 cubeNode395 cubeNode101 cubeNode1
def cubeNode397 : CubeTree := .branch .a cubeNode379 cubeNode383 cubeNode387 cubeNode396
def cubeNode398 : CubeTree := .branch .e cubeNode353 cubeNode372 cubeNode377 cubeNode397
def cubeNode399 : CubeTree := .branch .q cubeNode45 cubeNode45 cubeNode225 cubeNode267
def cubeNode400 : CubeTree := .branch .p cubeNode43 cubeNode43 cubeNode220 cubeNode399
def cubeNode401 : CubeTree := .branch .d cubeNode23 cubeNode23 cubeNode208 cubeNode400
def cubeNode402 : CubeTree := .branch .c cubeNode32 cubeNode32 cubeNode32 cubeNode401
def cubeNode403 : CubeTree := .branch .b cubeNode31 cubeNode31 cubeNode31 cubeNode402
def cubeNode404 : CubeTree := .branch .q cubeNode263 cubeNode45 cubeNode225 cubeNode263
def cubeNode405 : CubeTree := .branch .q cubeNode267 cubeNode45 cubeNode225 cubeNode267
def cubeNode406 : CubeTree := .branch .p cubeNode404 cubeNode43 cubeNode220 cubeNode405
def cubeNode407 : CubeTree := .branch .d cubeNode31 cubeNode41 cubeNode41 cubeNode406
def cubeNode408 : CubeTree := .branch .q cubeNode263 cubeNode45 cubeNode225 cubeNode267
def cubeNode409 : CubeTree := .branch .p cubeNode408 cubeNode43 cubeNode220 cubeNode405
def cubeNode410 : CubeTree := .branch .d cubeNode31 cubeNode41 cubeNode208 cubeNode409
def cubeNode411 : CubeTree := .branch .c cubeNode407 cubeNode32 cubeNode270 cubeNode410
def cubeNode412 : CubeTree := .branch .b cubeNode411 cubeNode206 cubeNode206 cubeNode276
def cubeNode413 : CubeTree := .branch .a cubeNode403 cubeNode23 cubeNode23 cubeNode412
def cubeNode414 : CubeTree := .branch .q cubeNode267 cubeNode225 cubeNode225 cubeNode225
def cubeNode415 : CubeTree := .branch .p cubeNode414 cubeNode220 cubeNode220 cubeNode220
def cubeNode416 : CubeTree := .branch .d cubeNode415 cubeNode208 cubeNode208 cubeNode208
def cubeNode417 : CubeTree := .branch .c cubeNode416 cubeNode207 cubeNode207 cubeNode207
def cubeNode418 : CubeTree := .branch .b cubeNode417 cubeNode256 cubeNode257 cubeNode236
def cubeNode419 : CubeTree := .branch .a cubeNode412 cubeNode236 cubeNode236 cubeNode418
def cubeNode420 : CubeTree := .branch .e cubeNode413 cubeNode280 cubeNode281 cubeNode419
def cubeNode421 : CubeTree := .branch .b cubeNode0 cubeNode257 cubeNode257 cubeNode257
def cubeNode422 : CubeTree := .branch .a cubeNode2 cubeNode2 cubeNode256 cubeNode421
def cubeNode423 : CubeTree := .branch .a cubeNode421 cubeNode257 cubeNode257 cubeNode257
def cubeNode424 : CubeTree := .branch .e cubeNode422 cubeNode260 cubeNode256 cubeNode423
def cubeNode425 : CubeTree := .branch .q cubeNode324 cubeNode324 cubeNode225 cubeNode110
def cubeNode426 : CubeTree := .branch .q cubeNode324 cubeNode389 cubeNode225 cubeNode110
def cubeNode427 : CubeTree := .branch .p cubeNode425 cubeNode426 cubeNode220 cubeNode88
def cubeNode428 : CubeTree := .branch .p cubeNode426 cubeNode426 cubeNode220 cubeNode88
def cubeNode429 : CubeTree := .branch .d cubeNode427 cubeNode428 cubeNode208 cubeNode87
def cubeNode430 : CubeTree := .branch .c cubeNode1 cubeNode429 cubeNode95 cubeNode95
def cubeNode431 : CubeTree := .branch .b cubeNode1 cubeNode430 cubeNode101 cubeNode101
def cubeNode432 : CubeTree := .branch .q cubeNode110 cubeNode324 cubeNode225 cubeNode110
def cubeNode433 : CubeTree := .branch .p cubeNode88 cubeNode432 cubeNode220 cubeNode88
def cubeNode434 : CubeTree := .branch .d cubeNode87 cubeNode433 cubeNode208 cubeNode87
def cubeNode435 : CubeTree := .branch .c cubeNode101 cubeNode434 cubeNode101 cubeNode101
def cubeNode436 : CubeTree := .branch .d cubeNode87 cubeNode208 cubeNode208 cubeNode208
def cubeNode437 : CubeTree := .branch .c cubeNode436 cubeNode207 cubeNode207 cubeNode207
def cubeNode438 : CubeTree := .branch .b cubeNode435 cubeNode437 cubeNode206 cubeNode206
def cubeNode439 : CubeTree := .branch .b cubeNode1 cubeNode236 cubeNode236 cubeNode236
def cubeNode440 : CubeTree := .branch .b cubeNode1 cubeNode236 cubeNode206 cubeNode236
def cubeNode441 : CubeTree := .branch .a cubeNode431 cubeNode438 cubeNode439 cubeNode440
def cubeNode442 : CubeTree := .branch .q cubeNode324 cubeNode225 cubeNode225 cubeNode225
def cubeNode443 : CubeTree := .branch .p cubeNode442 cubeNode220 cubeNode220 cubeNode220
def cubeNode444 : CubeTree := .branch .d cubeNode443 cubeNode208 cubeNode208 cubeNode208
def cubeNode445 : CubeTree := .branch .c cubeNode444 cubeNode207 cubeNode207 cubeNode207
def cubeNode446 : CubeTree := .branch .b cubeNode430 cubeNode445 cubeNode206 cubeNode206
def cubeNode447 : CubeTree := .branch .b cubeNode437 cubeNode236 cubeNode236 cubeNode236
def cubeNode448 : CubeTree := .branch .a cubeNode446 cubeNode447 cubeNode236 cubeNode236
def cubeNode449 : CubeTree := .branch .b cubeNode91 cubeNode279 cubeNode206 cubeNode279
def cubeNode450 : CubeTree := .branch .a cubeNode449 cubeNode279 cubeNode236 cubeNode279
def cubeNode451 : CubeTree := .branch .b cubeNode91 cubeNode279 cubeNode206 cubeNode206
def cubeNode452 : CubeTree := .branch .a cubeNode451 cubeNode279 cubeNode236 cubeNode236
def cubeNode453 : CubeTree := .branch .e cubeNode441 cubeNode448 cubeNode450 cubeNode452
def cubeNode454 : CubeTree := .branch .y cubeNode398 cubeNode420 cubeNode424 cubeNode453
def cubeNode455 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode91 cubeNode91
def cubeNode456 : CubeTree := .branch .b cubeNode101 cubeNode455 cubeNode91 cubeNode91
def cubeNode457 : CubeTree := .branch .c cubeNode116 cubeNode18 cubeNode91 cubeNode91
def cubeNode458 : CubeTree := .branch .b cubeNode116 cubeNode457 cubeNode91 cubeNode91
def cubeNode459 : CubeTree := .branch .b cubeNode116 cubeNode15 cubeNode91 cubeNode91
def cubeNode460 : CubeTree := .branch .a cubeNode1 cubeNode456 cubeNode458 cubeNode459
def cubeNode461 : CubeTree := .branch .d cubeNode1 cubeNode15 cubeNode1 cubeNode1
def cubeNode462 : CubeTree := .branch .c cubeNode1 cubeNode15 cubeNode461 cubeNode15
def cubeNode463 : CubeTree := .branch .b cubeNode1 cubeNode462 cubeNode155 cubeNode17
def cubeNode464 : CubeTree := .branch .c cubeNode101 cubeNode17 cubeNode101 cubeNode101
def cubeNode465 : CubeTree := .branch .p cubeNode88 cubeNode220 cubeNode249 cubeNode220
def cubeNode466 : CubeTree := .branch .d cubeNode26 cubeNode15 cubeNode465 cubeNode26
def cubeNode467 : CubeTree := .branch .c cubeNode24 cubeNode15 cubeNode466 cubeNode24
def cubeNode468 : CubeTree := .branch .b cubeNode464 cubeNode467 cubeNode162 cubeNode17
def cubeNode469 : CubeTree := .branch .c cubeNode116 cubeNode17 cubeNode101 cubeNode101
def cubeNode470 : CubeTree := .branch .p cubeNode88 cubeNode48 cubeNode111 cubeNode220
def cubeNode471 : CubeTree := .branch .d cubeNode87 cubeNode17 cubeNode470 cubeNode26
def cubeNode472 : CubeTree := .branch .c cubeNode24 cubeNode17 cubeNode471 cubeNode24
def cubeNode473 : CubeTree := .branch .d cubeNode87 cubeNode24 cubeNode140 cubeNode24
def cubeNode474 : CubeTree := .branch .c cubeNode95 cubeNode473 cubeNode1 cubeNode95
def cubeNode475 : CubeTree := .branch .c cubeNode95 cubeNode17 cubeNode101 cubeNode207
def cubeNode476 : CubeTree := .branch .b cubeNode469 cubeNode472 cubeNode474 cubeNode475
def cubeNode477 : CubeTree := .branch .c cubeNode95 cubeNode15 cubeNode1 cubeNode207
def cubeNode478 : CubeTree := .branch .b cubeNode15 cubeNode15 cubeNode477 cubeNode236
def cubeNode479 : CubeTree := .branch .a cubeNode463 cubeNode468 cubeNode476 cubeNode478
def cubeNode480 : CubeTree := .branch .c cubeNode1 cubeNode461 cubeNode1 cubeNode1
def cubeNode481 : CubeTree := .branch .b cubeNode1 cubeNode480 cubeNode1 cubeNode1
def cubeNode482 : CubeTree := .branch .q cubeNode110 cubeNode46 cubeNode46 cubeNode225
def cubeNode483 : CubeTree := .branch .p cubeNode88 cubeNode48 cubeNode482 cubeNode220
def cubeNode484 : CubeTree := .branch .d cubeNode26 cubeNode15 cubeNode483 cubeNode26
def cubeNode485 : CubeTree := .branch .d cubeNode87 cubeNode111 cubeNode87 cubeNode87
def cubeNode486 : CubeTree := .branch .c cubeNode95 cubeNode484 cubeNode485 cubeNode95
def cubeNode487 : CubeTree := .branch .c cubeNode116 cubeNode161 cubeNode101 cubeNode101
def cubeNode488 : CubeTree := .branch .b cubeNode101 cubeNode486 cubeNode487 cubeNode101
def cubeNode489 : CubeTree := .branch .c cubeNode95 cubeNode471 cubeNode1 cubeNode95
def cubeNode490 : CubeTree := .branch .b cubeNode101 cubeNode489 cubeNode1 cubeNode101
def cubeNode491 : CubeTree := .branch .b cubeNode101 cubeNode477 cubeNode1 cubeNode236
def cubeNode492 : CubeTree := .branch .a cubeNode481 cubeNode488 cubeNode490 cubeNode491
def cubeNode493 : CubeTree := .branch .b cubeNode1 cubeNode18 cubeNode1 cubeNode1
def cubeNode494 : CubeTree := .branch .b cubeNode101 cubeNode18 cubeNode91 cubeNode206
def cubeNode495 : CubeTree := .branch .c cubeNode95 cubeNode18 cubeNode91 cubeNode207
def cubeNode496 : CubeTree := .branch .b cubeNode101 cubeNode495 cubeNode91 cubeNode206
def cubeNode497 : CubeTree := .branch .a cubeNode493 cubeNode494 cubeNode496 cubeNode1
def cubeNode498 : CubeTree := .branch .e cubeNode460 cubeNode479 cubeNode492 cubeNode497
def cubeNode499 : CubeTree := .leaf (.dom (alloc .one .two .four .one .three .three .four .three .four))
def cubeNode500 : CubeTree := .branch .q cubeNode499 cubeNode45 cubeNode499 cubeNode44
def cubeNode501 : CubeTree := .branch .q cubeNode43 cubeNode43 cubeNode43 cubeNode44
def cubeNode502 : CubeTree := .branch .q cubeNode499 cubeNode45 cubeNode46 cubeNode44
def cubeNode503 : CubeTree := .branch .p cubeNode500 cubeNode501 cubeNode502 cubeNode42
def cubeNode504 : CubeTree := .branch .d cubeNode15 cubeNode26 cubeNode503 cubeNode26
def cubeNode505 : CubeTree := .branch .c cubeNode15 cubeNode24 cubeNode504 cubeNode24
def cubeNode506 : CubeTree := .branch .q cubeNode31 cubeNode225 cubeNode31 cubeNode225
def cubeNode507 : CubeTree := .branch .p cubeNode506 cubeNode220 cubeNode506 cubeNode220
def cubeNode508 : CubeTree := .branch .d cubeNode15 cubeNode208 cubeNode507 cubeNode208
def cubeNode509 : CubeTree := .branch .c cubeNode15 cubeNode207 cubeNode508 cubeNode17
def cubeNode510 : CubeTree := .branch .q cubeNode46 cubeNode45 cubeNode46 cubeNode225
def cubeNode511 : CubeTree := .branch .q cubeNode43 cubeNode43 cubeNode43 cubeNode225
def cubeNode512 : CubeTree := .branch .p cubeNode510 cubeNode511 cubeNode510 cubeNode220
def cubeNode513 : CubeTree := .branch .d cubeNode15 cubeNode26 cubeNode512 cubeNode208
def cubeNode514 : CubeTree := .branch .c cubeNode15 cubeNode24 cubeNode513 cubeNode24
def cubeNode515 : CubeTree := .branch .b cubeNode505 cubeNode509 cubeNode514 cubeNode17
def cubeNode516 : CubeTree := .branch .q cubeNode23 cubeNode225 cubeNode23 cubeNode225
def cubeNode517 : CubeTree := .branch .p cubeNode516 cubeNode220 cubeNode516 cubeNode220
def cubeNode518 : CubeTree := .branch .d cubeNode17 cubeNode208 cubeNode517 cubeNode208
def cubeNode519 : CubeTree := .branch .c cubeNode17 cubeNode207 cubeNode518 cubeNode15
def cubeNode520 : CubeTree := .branch .b cubeNode519 cubeNode236 cubeNode236 cubeNode236
def cubeNode521 : CubeTree := .branch .d cubeNode17 cubeNode26 cubeNode512 cubeNode208
def cubeNode522 : CubeTree := .branch .c cubeNode17 cubeNode24 cubeNode521 cubeNode24
def cubeNode523 : CubeTree := .branch .b cubeNode522 cubeNode206 cubeNode313 cubeNode206
def cubeNode524 : CubeTree := .branch .b cubeNode15 cubeNode206 cubeNode236 cubeNode236
def cubeNode525 : CubeTree := .branch .a cubeNode515 cubeNode520 cubeNode523 cubeNode524
def cubeNode526 : CubeTree := .branch .q cubeNode16 cubeNode225 cubeNode16 cubeNode225
def cubeNode527 : CubeTree := .branch .p cubeNode526 cubeNode220 cubeNode526 cubeNode220
def cubeNode528 : CubeTree := .branch .d cubeNode18 cubeNode208 cubeNode527 cubeNode208
def cubeNode529 : CubeTree := .branch .c cubeNode18 cubeNode207 cubeNode528 cubeNode18
def cubeNode530 : CubeTree := .branch .b cubeNode529 cubeNode206 cubeNode279 cubeNode279
def cubeNode531 : CubeTree := .branch .a cubeNode530 cubeNode236 cubeNode279 cubeNode279
def cubeNode532 : CubeTree := .branch .d cubeNode15 cubeNode26 cubeNode512 cubeNode26
def cubeNode533 : CubeTree := .branch .q cubeNode32 cubeNode44 cubeNode32 cubeNode225
def cubeNode534 : CubeTree := .branch .p cubeNode533 cubeNode42 cubeNode533 cubeNode220
def cubeNode535 : CubeTree := .branch .d cubeNode24 cubeNode3 cubeNode534 cubeNode208
def cubeNode536 : CubeTree := .branch .q cubeNode41 cubeNode44 cubeNode41 cubeNode225
def cubeNode537 : CubeTree := .branch .p cubeNode536 cubeNode42 cubeNode536 cubeNode220
def cubeNode538 : CubeTree := .leaf (.dom (alloc .three .two .one .one .three .four .four .one .four))
def cubeNode539 : CubeTree := .branch .q cubeNode263 cubeNode45 cubeNode538 cubeNode225
def cubeNode540 : CubeTree := .branch .q cubeNode538 cubeNode45 cubeNode538 cubeNode225
def cubeNode541 : CubeTree := .branch .p cubeNode539 cubeNode511 cubeNode540 cubeNode220
def cubeNode542 : CubeTree := .branch .d cubeNode512 cubeNode537 cubeNode541 cubeNode208
def cubeNode543 : CubeTree := .branch .c cubeNode532 cubeNode535 cubeNode542 cubeNode24
def cubeNode544 : CubeTree := .branch .b cubeNode543 cubeNode206 cubeNode337 cubeNode206
def cubeNode545 : CubeTree := .branch .b cubeNode340 cubeNode256 cubeNode236 cubeNode236
def cubeNode546 : CubeTree := .branch .a cubeNode544 cubeNode236 cubeNode545 cubeNode236
def cubeNode547 : CubeTree := .branch .b cubeNode18 cubeNode206 cubeNode279 cubeNode206
def cubeNode548 : CubeTree := .branch .a cubeNode547 cubeNode236 cubeNode279 cubeNode236
def cubeNode549 : CubeTree := .branch .e cubeNode525 cubeNode531 cubeNode546 cubeNode548
def cubeNode550 : CubeTree := .branch .p cubeNode111 cubeNode267 cubeNode88 cubeNode220
def cubeNode551 : CubeTree := .branch .q cubeNode46 cubeNode46 cubeNode110 cubeNode225
def cubeNode552 : CubeTree := .branch .p cubeNode551 cubeNode267 cubeNode88 cubeNode220
def cubeNode553 : CubeTree := .branch .d cubeNode550 cubeNode552 cubeNode87 cubeNode208
def cubeNode554 : CubeTree := .branch .c cubeNode1 cubeNode553 cubeNode95 cubeNode95
def cubeNode555 : CubeTree := .branch .b cubeNode1 cubeNode554 cubeNode101 cubeNode101
def cubeNode556 : CubeTree := .branch .d cubeNode87 cubeNode324 cubeNode87 cubeNode208
def cubeNode557 : CubeTree := .branch .c cubeNode101 cubeNode556 cubeNode101 cubeNode101
def cubeNode558 : CubeTree := .branch .b cubeNode557 cubeNode437 cubeNode206 cubeNode206
def cubeNode559 : CubeTree := .branch .a cubeNode555 cubeNode558 cubeNode439 cubeNode440
def cubeNode560 : CubeTree := .branch .q cubeNode46 cubeNode44 cubeNode110 cubeNode225
def cubeNode561 : CubeTree := .branch .p cubeNode560 cubeNode42 cubeNode88 cubeNode220
def cubeNode562 : CubeTree := .branch .d cubeNode550 cubeNode561 cubeNode87 cubeNode208
def cubeNode563 : CubeTree := .branch .c cubeNode1 cubeNode562 cubeNode95 cubeNode95
def cubeNode564 : CubeTree := .branch .d cubeNode389 cubeNode208 cubeNode208 cubeNode208
def cubeNode565 : CubeTree := .branch .c cubeNode564 cubeNode207 cubeNode207 cubeNode207
def cubeNode566 : CubeTree := .branch .b cubeNode563 cubeNode565 cubeNode206 cubeNode206
def cubeNode567 : CubeTree := .branch .a cubeNode566 cubeNode447 cubeNode236 cubeNode236
def cubeNode568 : CubeTree := .branch .e cubeNode559 cubeNode567 cubeNode450 cubeNode452
def cubeNode569 : CubeTree := .branch .b cubeNode1 cubeNode3 cubeNode0 cubeNode256
def cubeNode570 : CubeTree := .branch .a cubeNode569 cubeNode421 cubeNode421 cubeNode256
def cubeNode571 : CubeTree := .branch .e cubeNode570 cubeNode261 cubeNode423 cubeNode256
def cubeNode572 : CubeTree := .branch .y cubeNode498 cubeNode549 cubeNode568 cubeNode571
def cubeNode573 : CubeTree := .branch .x cubeNode200 cubeNode350 cubeNode454 cubeNode572

def cubeTree : CubeTree := cubeNode573

theorem cubeTree_valid : validTree emptyPartial cubeTree = true := by
  decide +kernel

end ParetoEFX296.Approx.P034

open ParetoEFX296.Approx

theorem solution (K : ℕ) (hK : 6 ≤ K) :
    (∀ (i : Agent) (g : Good), 0 < inst K i g) ∧
    ∀ α : ℝ, (2 : ℝ) / 3 + 1 / (K : ℝ) < α →
      ¬ ∃ A : Allocation Agent Good,
        IsAlphaEFX (inst K) α A ∧ IsParetoOptimal (inst K) A := by
  exact P034.theorem_from_certificate P034.cubeTree P034.cubeTree_valid K hK

#print axioms solution
