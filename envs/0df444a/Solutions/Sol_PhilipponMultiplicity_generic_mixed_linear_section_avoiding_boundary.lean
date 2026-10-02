-- Prove2me | solution 1 for PhilipponMultiplicity.generic_mixed_linear_section_avoiding_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T14:00:49.841014+00:00
-- url     : https://prove2.me/submissions/32b6aaf2-e15c-4103-8b89-8d1692fdea9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_filter_regular_mixed_section
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertFunction_colon_add
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

/-- Colon by a multihomogeneous element preserves the actual grading. -/
theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h


end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d


end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) +
        aeval (fun i => X i - C (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P})) := by
  let J := I ⊔ Ideal.span {P}
  let Q := I.colon {P}
  obtain ⟨a, ha⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension J
    (multigraded_hilbert_polynomial_exists K M J (homogeneous_sup_span M I hI P D hP))
  obtain ⟨b, hb⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q (homogeneous_colon M I hI P D hP))
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨D + a + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have han : ∀ i, a i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have hbsub : ∀ i, b i ≤ (n - D) i := by
    intro i; have := hn i; change D i + a i + b i ≤ n i at this; change b i ≤ n i - D i; omega
  have hnsub : D + (n - D) = n := by
    funext i; exact Nat.add_sub_of_le (hDn i)
  have heval (F : MvPolynomial M.FactorIndex ℚ) :
      eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
        eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    clear ha hb
    induction F using MvPolynomial.induction_on with
    | C c => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
      simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
      simp only [Pi.sub_apply, Nat.cast_sub (hDn i)]
  rw [map_add, heval, ha n han, hb (n - D) hbsub]
  have h := hilbertFunction_colon_add M I hI P D hP (n - D)
  rw [hnsub] at h
  exact_mod_cast h


end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


end PhilipponMultiplicity
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι]

def shift (D : ι → ℚ) : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  aeval (fun i => X i - C (D i))

def deriv (D : ι → ℚ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, D i • (pderiv i).toLinearMap

theorem deriv_apply (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    deriv D F = ∑ i, D i • pderiv i F := by
  simp only [deriv, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem deriv_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (i : ι) :
    deriv D (F * X i) = deriv D F * X i + D i • F := by
  classical
  simp only [deriv_apply, pderiv_mul, pderiv_X, MvPolynomial.smul_eq_C_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp [Pi.single_apply, mul_ite, mul_assoc]

private theorem component_mul_X (F : MvPolynomial ι ℚ) (i : ι) (n : ℕ) :
    homogeneousComponent (n + 1) (F * X i) = homogeneousComponent n F * X i := by
  classical
  letI := weightedGradedAlgebra ℚ (1 : ι → ℕ)
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule ℚ (1 : ι → ℕ))
    (a := F) (i := n) (isHomogeneous_X ℚ i)
  change ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) (F * X i)) (n + 1) : MvPolynomial ι ℚ) =
    ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) F) n : MvPolynomial ι ℚ) * X i at h
  simpa only [MvPolynomial.decompose'_apply, homogeneousComponent] using h

private theorem degree_le_pred_of_top_zero (F : MvPolynomial ι ℚ) (n : ℕ)
    (hdegree : F.totalDegree ≤ n) (hzero : homogeneousComponent n F = 0) :
    F.totalDegree ≤ n - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hdegree
  have hne : d.degree ≠ n := by
    intro heq
    have hh := congrArg (coeff d) hzero
    simp only [coeff_homogeneousComponent, heq, if_pos rfl, coeff_zero] at hh
    exact (mem_support_iff.mp hd) hh
  change d.degree ≤ n - 1
  omega

private def Expansion (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ) : Prop :=
  (shift D F).totalDegree ≤ n ∧ homogeneousComponent n (shift D F) = F ∧
    (∀ k, n = k + 1 → homogeneousComponent k (shift D F) = -deriv D F)

private theorem expansion_C (D : ι → ℚ) (c : ℚ) : Expansion D (C c) 0 := by
  simp [Expansion, shift]

private theorem expansion_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hF : F.IsHomogeneous n) (h : Expansion D F n) (i : ι) :
    Expansion D (F * X i) (n + 1) := by
  classical
  rcases h with ⟨hdeg, htop, hnext⟩
  have hs : shift D (F * X i) = shift D F * X i - D i • shift D F := by
    simp only [shift, map_mul, aeval_X, mul_sub, MvPolynomial.smul_eq_C_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right hdeg 1)
    · exact (totalDegree_smul_le _ _).trans (hdeg.trans (Nat.le_succ n))
  · rw [hs, map_sub, map_smul, component_mul_X, htop,
      homogeneousComponent_eq_zero _ _ (by omega : (shift D F).totalDegree < n + 1)]
    simp
  · intro k hk
    have hkn : k = n := by omega
    subst k
    rw [hs, map_sub, map_smul, htop, deriv_mul_X]
    cases n with
    | zero =>
      have hconst : F = C (coeff 0 F) := by
        exact (homogeneousComponent_eq_self hF).symm.trans
          (MvPolynomial.homogeneousComponent_zero F)
      have hd : deriv D F = 0 := by
        nth_rw 1 [hconst]
        simp [deriv]
      have hz : coeff (0 : ι →₀ ℕ) (shift D F * X i) = 0 := by
        simpa using (MvPolynomial.coeff_mul_X' (0 : ι →₀ ℕ) i (shift D F))
      simp [hd, homogeneousComponent_zero, hz]
    | succ n =>
      rw [component_mul_X, hnext n rfl]
      simp only [neg_mul, neg_add_rev, sub_eq_add_neg]
      ac_rfl

private theorem expansion_monomial (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    Expansion D (monomial a c) a.degree := by
  classical
  induction a using Finsupp.induction with
  | zero => simpa using expansion_C D c
  | @single_add i k a hia hk ih =>
    have haux : ∀ k, Expansion D (monomial (Finsupp.single i k + a) c)
        ((Finsupp.single i k + a).degree) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        have heq : monomial (Finsupp.single i (k + 1) + a) c =
            monomial (Finsupp.single i k + a) c * X i := by
          simp only [monomial_single_add, pow_succ]
          ring
        rw [heq]
        have hh := expansion_mul_X D (monomial (Finsupp.single i k + a) c)
          (Finsupp.single i k + a).degree (isHomogeneous_monomial c rfl) ihk i
        simpa only [map_add, Finsupp.degree_single, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
    exact haux k

private theorem monomial_difference (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree - 1 ∧
    (a.degree = 0 → monomial a c - shift D (monomial a c) = 0) ∧
    (0 < a.degree → homogeneousComponent (a.degree - 1)
      (monomial a c - shift D (monomial a c)) = deriv D (monomial a c)) := by
  obtain ⟨hdeg, htop, hnext⟩ := expansion_monomial D a c
  have hhom := isHomogeneous_monomial (σ := ι) c (show a.degree = a.degree from rfl)
  have hbd : (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree :=
    (totalDegree_sub _ _).trans (max_le hhom.totalDegree_le hdeg)
  refine ⟨degree_le_pred_of_top_zero _ _ hbd ?_, ?_, ?_⟩
  · rw [map_sub, homogeneousComponent_eq_self hhom, htop, sub_self]
  · intro ha
    have hconst : monomial a c = C (coeff 0 (monomial a c)) :=
      (homogeneousComponent_eq_self (ha ▸ hhom)).symm.trans
        (MvPolynomial.homogeneousComponent_zero _)
    conv_lhs => rw [hconst]
    simp [shift]
  · intro ha
    rw [map_sub, homogeneousComponent_of_mem hhom,
      if_neg (by omega), hnext (a.degree - 1) (by omega)]
    simp

/-- Translation subtracts the top degree, and its next homogeneous part is
the directional derivative of the old top part. -/
theorem top_difference (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (ha : 0 < a) (hF : F.totalDegree ≤ a) :
    (F - shift D F).totalDegree ≤ a - 1 ∧
    homogeneousComponent (a - 1) (F - shift D F) =
      deriv D (homogeneousComponent a F) := by
  classical
  let δ : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
    LinearMap.id - (shift D).toLinearMap
  have hδ : δ F = F - shift D F := rfl
  have hsum : F - shift D F = ∑ d ∈ F.support, δ (monomial d (coeff d F)) := by
    rw [← hδ, ← map_sum]
    congr 1
    exact F.as_sum
  have hterm (d : ι →₀ ℕ) (hd : d ∈ F.support) :
      (δ (monomial d (coeff d F))).totalDegree ≤ a - 1 ∧
      homogeneousComponent (a - 1) (δ (monomial d (coeff d F))) =
        deriv D (homogeneousComponent a (monomial d (coeff d F))) := by
    obtain ⟨hdeg, hz, ht⟩ := monomial_difference D d (coeff d F)
    have hda : d.degree ≤ a := (le_totalDegree hd).trans hF
    refine ⟨hdeg.trans (Nat.sub_le_sub_right hda 1), ?_⟩
    change homogeneousComponent (a - 1) (monomial d (coeff d F) - shift D (monomial d (coeff d F))) = _
    by_cases heq : d.degree = a
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_pos heq.symm, ← heq]
      exact ht (heq ▸ ha)
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_neg (Ne.symm heq), map_zero]
      by_cases hd0 : d.degree = 0
      · rw [hz hd0, map_zero]
      · exact homogeneousComponent_eq_zero _ _ (by omega)
  constructor
  · rw [hsum]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun d hd => (hterm d hd).1))
  · rw [hsum, map_sum]
    conv_rhs => rw [F.as_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun d hd => (hterm d hd).2)


end PhilipponMultiplicity.FiniteDifference
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def countIndex (l : List ι) : ι →₀ ℕ :=
  (l.map (fun i => Finsupp.single i 1)).sum

def mixedDifference (l : List ι) (F : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  l.foldl (fun P i => P - shift (Pi.single i 1) P) F

theorem countIndex_apply (l : List ι) (i : ι) : countIndex l i = l.count i := by
  induction l with
  | nil => simp [countIndex]
  | cons j l ih =>
    by_cases h : i = j
    · subst j
      simp [countIndex, List.count_cons, ← ih, Nat.add_comm]
    · simp [countIndex, List.count_cons, h, Ne.symm h, ← ih]

theorem countIndex_cons (i : ι) (l : List ι) :
    countIndex (i :: l) = countIndex l + Finsupp.single i 1 := by
  simp [countIndex, add_comm]

theorem degree_countIndex (l : List ι) : (countIndex l).degree = l.length := by
  induction l with
  | nil => simp [countIndex]
  | cons i l ih => simp [countIndex_cons, ih]

theorem sum_count (l : List ι) : ∑ i, l.count i = l.length := by
  simpa only [← countIndex_apply, ← Finsupp.degree_eq_sum] using degree_countIndex l

theorem factorial_count_cons (i : ι) (l : List ι) :
    (∏ j : ι, (((i :: l).count j).factorial : ℚ)) =
      (l.count i + 1 : ℚ) * ∏ j : ι, ((l.count j).factorial : ℚ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((l.count j).factorial : ℚ))
        (Finset.mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i, (((i :: l).count j).factorial : ℚ)) =
      ∏ j ∈ Finset.univ.erase i, ((l.count j).factorial : ℚ) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [List.count_cons, hji, Ne.symm hji]
  rw [hprod, List.count_cons_self, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

theorem deriv_single (i : ι) (F : MvPolynomial ι ℚ) :
    deriv (Pi.single i 1) F = pderiv i F := by
  classical
  rw [deriv_apply]
  simp [Pi.single_apply]

/-- A full mixed finite difference extracts the normalized top coefficient.
Lower total degrees vanish; zero coefficients and repeated block directions
are allowed, with no positivity hypothesis. -/
theorem mixedDifference_eq_constant (l : List ι) (F : MvPolynomial ι ℚ)
    (hF : F.totalDegree ≤ l.length) :
    mixedDifference l F =
      C (coeff (countIndex l) F * ∏ i, ((l.count i).factorial : ℚ)) := by
  induction l generalizing F with
  | nil =>
    have h0 : F.totalDegree = 0 := Nat.eq_zero_of_le_zero hF
    simpa [mixedDifference, countIndex] using
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0)
  | cons i l ih =>
    have htop := top_difference (Pi.single i 1) F (l.length + 1) (by omega) hF
    have hdeg : (F - shift (Pi.single i 1) F).totalDegree ≤ l.length := by
      simpa using htop.1
    change mixedDifference l (F - shift (Pi.single i 1) F) = _
    rw [ih _ hdeg]
    have hc : coeff (countIndex l) (F - shift (Pi.single i 1) F) =
        coeff (countIndex (i :: l)) F * (l.count i + 1 : ℚ) := by
      have h := congrArg (coeff (countIndex l)) htop.2
      simp only [Nat.add_sub_cancel, deriv_single, coeff_pderiv,
        coeff_homogeneousComponent, degree_countIndex, if_pos rfl,
        countIndex_apply] at h
      simpa [countIndex_cons, degree_countIndex] using h
    rw [hc, factorial_count_cons]
    congr 1
    ring

end PhilipponMultiplicity.FiniteDifference
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Only membership on the selected homogeneous piece matters for its
quotient Hilbert function. No global equality of the two ideals is needed. -/
theorem hilbertFunction_eq_of_homogeneous_mem_iff
    (I J : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hmem : ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J)) :
    hilbertFunction K M.factorCount M.ambientDimension I D =
      hilbertFunction K M.factorCount M.ambientDimension J D := by
  let V := degreePiece K M.factorCount M.ambientDimension D
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem P.val ((M.degreePiece_iff _ _).mp P.property)
  have hrange (A : Ideal M.CoordinateRing) :
      LinearMap.range ((Ideal.Quotient.mkₐ K A).toLinearMap.domRestrict V) =
        V.map (Ideal.Quotient.mkₐ K A).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)).finrank_eq
  rw [hrange I,hrange J] at he
  exact he

/-- Equality in all sufficiently large block degrees preserves the actual
eventual quotient Hilbert polynomial. -/
theorem hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff
    (I J : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hmem : ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
      ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J)) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension J := by
  obtain ⟨F,hF⟩ := multigraded_hilbert_polynomial_exists K M I hI
  obtain ⟨a,ha⟩ := hF
  obtain ⟨b,hb⟩ := hmem
  have hJ : IsHilbertPolynomial K M.factorCount M.ambientDimension J F := by
    refine ⟨fun i => max (a i) (b i),?_⟩
    intro D hD
    rw [ha D (fun i => (le_max_left _ _).trans (hD i)),
      hilbertFunction_eq_of_homogeneous_mem_iff M I J D
        (hb D (fun i => (le_max_right _ _).trans (hD i)))]
  rw [hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension I ⟨a,ha⟩,
      hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension J hJ]

/-- Filter regularity removes the multiplication kernel in large degrees,
even if the equation is a zero divisor on irrelevant components. -/
theorem hilbertPolynomial_colon_eq_of_eventual_injective
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing)
    (hinj : ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
      ∀ Q, M.IsHomogeneous Q D → P * Q ∈ I → Q ∈ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P}) =
      hilbertPolynomial K M.factorCount M.ambientDimension I := by
  symm
  apply hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff M I _ hI
  obtain ⟨B,hB⟩ := hinj
  refine ⟨B,?_⟩
  intro D hD Q hQ
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm Q P]
  exact ⟨fun h => I.mul_mem_left P h,hB D hD Q hQ⟩

theorem hilbertPolynomial_filter_regular_cut
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hinj : ∃ B : M.FactorIndex → ℕ, ∀ E, (∀ i, B i ≤ E i) →
      ∀ Q, M.IsHomogeneous Q E → P * Q ∈ I → Q ∈ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) =
      hilbertPolynomial K M.factorCount M.ambientDimension I -
        FiniteDifference.shift (fun i => (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension I) := by
  have h := hilbertPolynomial_colon_add M I hI P D hP
  rw [hilbertPolynomial_colon_eq_of_eventual_injective M I hI P hinj] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem homogeneous_cut_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧ J (k+1) = J k ⊔ Ideal.span {P k}) :
    ∀ k ≤ l.length, IsMultihomogeneousIdeal M (J k) := by
  intro k
  induction k with
  | zero => exact fun _ => hzero
  | succ k ih =>
    intro hk
    obtain ⟨hP,hJ⟩ := hstep k (by omega)
    rw [hJ]
    exact homogeneous_sup_span M _ (ih (by omega)) _ _ hP

/-- Iterate the exact-sequence computation along a flag, retaining the full
Hilbert polynomial until the final coefficient extraction. -/
theorem hilbertPolynomial_filter_regular_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
      J (k+1) = J k ⊔ Ideal.span {P k} ∧
      ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
        ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) :
    hilbertPolynomial K M.factorCount M.ambientDimension (J l.length) =
      FiniteDifference.mixedDifference l
        (hilbertPolynomial K M.factorCount M.ambientDimension (J 0)) := by
  classical
  have hhom := homogeneous_cut_chain M l J P hzero
    (fun k hk => ⟨(hstep k hk).1,(hstep k hk).2.1⟩)
  have haux : ∀ k ≤ l.length,
      hilbertPolynomial K M.factorCount M.ambientDimension (J k) =
        FiniteDifference.mixedDifference (l.take k)
          (hilbertPolynomial K M.factorCount M.ambientDimension (J 0)) := by
    intro k
    induction k with
    | zero => intro _; simp [FiniteDifference.mixedDifference]
    | succ k ih =>
      intro hk
      have hkl : k < l.length := by omega
      obtain ⟨hP,hJ,hinj⟩ := hstep k hkl
      rw [hJ,hilbertPolynomial_filter_regular_cut M _ (hhom k (by omega)) _ _ hP hinj,
        ih (by omega),List.take_succ_eq_append_getElem hkl]
      have hcast : (fun i => ((Pi.single (M := fun _ : M.FactorIndex => ℕ) l[k] 1 i : ℕ) : ℚ)) =
          Pi.single (M := fun _ : M.FactorIndex => ℚ) l[k] 1 := by
        funext i
        simp [Pi.single_apply]
      rw [hcast]
      simp only [FiniteDifference.mixedDifference,List.foldl_append,List.foldl_cons,List.foldl_nil]
  simpa only [List.take_length] using haux l.length le_rfl

theorem degreeValue_of_constant_hilbertPolynomial
    (I : Ideal M.CoordinateRing) (c : ℚ)
    (hP : hilbertPolynomial K M.factorCount M.ambientDimension I = C c)
    (D : M.FactorIndex → ℕ) :
    degreeValue K M.factorCount M.ambientDimension I D = c := by
  unfold degreeValue degreeForm
  rw [hP]
  dsimp only
  rw [totalDegree_C]
  simp only [Nat.factorial_zero,Nat.cast_one,one_smul,homogeneousComponent_zero,
    coeff_C,ite_true,eval_C]

end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

/-- The numerical part of a general mixed section follows from a genuine
filter-regular flag and eventual equality with the reduced final ideal. -/
theorem generic_mixed_section_of_filter_regular_choice
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchoice : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L)))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        locusDegreeValue M (linearSlice M W L) (fun _ => 1) =
          idealMixedDegree M (M.vanishingIdeal W) α := by
  classical
  intro M W hW hirr α hα hsum B hB hBW hproper
  obtain ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,hfirst,hstep,hlast⟩ :=
    hchoice M W hW hirr α hα hsum B hB hBW hproper
  refine ⟨L,hL,hfinite,hdisjoint,?_⟩
  have hhom0 : IsMultihomogeneousIdeal M (J 0) := by
    rw [hfirst]
    exact vanishingIdeal_multihomogeneous K M W
  have hhom := Hilbert.homogeneous_cut_chain M l J P hhom0
    (fun k hk => ⟨(hstep k hk).1,(hstep k hk).2.1⟩)
  have heq := Hilbert.hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff M
    (J l.length) (M.vanishingIdeal (linearSlice M W L)) (hhom _ le_rfl) hlast
  have hpoly := Hilbert.hilbertPolynomial_filter_regular_chain M l J P hhom0 hstep
  have hlen : l.length = ∑ i, α i := by
    rw [← FiniteDifference.sum_count l]
    exact Finset.sum_congr rfl (fun i _ => hcount i)
  have hdegree : (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (J 0)).totalDegree ≤ l.length := by
    rw [hfirst,hlen,hsum]
    exact le_rfl
  rw [FiniteDifference.mixedDifference_eq_constant l _ hdegree,hfirst] at hpoly
  have hindex : FiniteDifference.countIndex l = Finsupp.equivFunOnFinite.symm α := by
    ext i
    change FiniteDifference.countIndex l i = α i
    rw [FiniteDifference.countIndex_apply,hcount i]
  have hconst : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal (linearSlice M W L)) =
        C (idealMixedDegree M (M.vanishingIdeal W) α) := by
    rw [← heq,hpoly,hindex]
    unfold idealMixedDegree
    change ∑ i, α i = idealDimension M (M.vanishingIdeal W) at hsum
    rw [if_pos hsum]
    simp only [hcount]
  exact Hilbert.degreeValue_of_constant_hilbertPolynomial M _ _ hconst (fun _ => 1)

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        locusDegreeValue M (linearSlice M W L) (fun _ => 1) =
          idealMixedDegree M (M.vanishingIdeal W) α := by
  exact generic_mixed_section_of_filter_regular_choice K hK
    (exists_filter_regular_mixed_section K hK)
