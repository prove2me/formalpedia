-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_3_1_of_hilbert_data
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T22:38:42.597267+00:00
-- url     : https://prove2.me/submissions/954b117c-3974-47f8-b9ac-0f427394a51d

import Theorems.Thm_PhilipponMultiplicity_regular_hypersurface_hilbert_function
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponFiniteDifference.lean

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

theorem coeff_deriv (D : ι → ℚ) (F : MvPolynomial ι ℚ) (b : ι →₀ ℕ) :
    coeff b (deriv D F) =
      ∑ i, D i * (coeff (b + Finsupp.single i 1) F * (b i + 1 : ℚ)) := by
  classical
  rw [deriv_apply]
  change coeff b (∑ i, D i • pderiv i F) = _
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_pderiv]

theorem deriv_ne_zero (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (a : ℕ) (ha : 0 < a)
    (hF : F.IsHomogeneous a) (hne : F ≠ 0)
    (hcoeff : ∀ b, 0 ≤ coeff b F) : deriv D F ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := exists_coeff_ne_zero hne
  have hba : b.degree = a := by
    by_contra h
    exact hb (hF.coeff_eq_zero h)
  have hsum : 0 < ∑ i, b i := by
    simpa only [← Finsupp.degree_eq_sum, hba] using ha
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  let c := b - Finsupp.single i 1
  have hc : c + Finsupp.single i 1 = b := by
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr (by omega)
  have hpos : 0 < coeff c (deriv D F) := by
    rw [coeff_deriv]
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hD j).le (mul_nonneg (hcoeff _) (by positivity))
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hc]
      exact mul_pos (hD i) (mul_pos (lt_of_le_of_ne (hcoeff b) (Ne.symm hb)) (by positivity))
  intro hz
  rw [hz, coeff_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Positive equation degrees prevent cancellation of the new leading part. -/
theorem difference_degree (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (ha : 0 < F.totalDegree)
    (hcoeff : ∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) :
    (F - shift D F).totalDegree = F.totalDegree - 1 ∧
    homogeneousComponent (F - shift D F).totalDegree (F - shift D F) =
      deriv D (homogeneousComponent F.totalDegree F) := by
  obtain ⟨hdeg, htop⟩ := top_difference D F F.totalDegree ha le_rfl
  have hne : homogeneousComponent F.totalDegree F ≠ 0 := by
    intro hz
    have hh := degree_le_pred_of_top_zero F F.totalDegree le_rfl hz
    omega
  have hdne := deriv_ne_zero D hD _ F.totalDegree ha
    (homogeneousComponent_isHomogeneous _ _) hne hcoeff
  have hge : F.totalDegree - 1 ≤ (F - shift D F).totalDegree := by
    by_contra h
    have hz := homogeneousComponent_eq_zero (F.totalDegree - 1) (F - shift D F)
      (lt_of_not_ge h)
    exact hdne (htop.symm.trans hz)
  have heq := le_antisymm hdeg hge
  exact ⟨heq, heq ▸ htop⟩

theorem eval_deriv_monomial (D d : ι → ℚ) (hd : ∀ i, d i ≠ 0)
    (b : ι →₀ ℕ) (c : ℚ) :
    eval d (deriv D (monomial b c)) =
      c * (∑ i, (b i : ℚ) * D i / d i) * ∏ i, d i ^ b i := by
  classical
  have hev (i : ι) : eval d (pderiv i (monomial b c)) =
      (b i : ℚ) * eval d (monomial b c) / d i := by
    apply (eq_div_iff (hd i)).mpr
    have hh := congrArg (eval d) (X_mul_pderiv_monomial (i := i) (m := b) (r := c))
    simpa only [map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast, mul_comm] using hh
  rw [deriv_apply]
  change eval d (∑ i, D i • pderiv i (monomial b c)) = _
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, hev, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_deriv_self (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (hF : F.IsHomogeneous a) : eval D (deriv D F) = (a : ℚ) * eval D F := by
  classical
  have hh := congrArg (eval D) hF.sum_X_mul_pderiv
  rw [deriv_apply]
  change eval D (∑ i, D i • pderiv i F) = _
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_X, map_nsmul,
    nsmul_eq_mul, map_natCast] using hh

end PhilipponMultiplicity.FiniteDifference

end

noncomputable section
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem IsHilbertPolynomial.hypersurface
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (F : MvPolynomial M.FactorIndex ℚ)
    (hF : IsHilbertPolynomial K M.factorCount M.ambientDimension I F) :
    IsHilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})
      (F - aeval (fun i => X i - C (D i : ℚ)) F) := by
  obtain ⟨b, hb⟩ := hF
  refine ⟨D + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := fun i => (Nat.le_add_right _ _).trans (hn i)
  have hbn : ∀ i, b i ≤ n i := fun i => (Nat.le_add_left _ _).trans (hn i)
  have hbsub : ∀ i, b i ≤ n i - D i := by
    intro i
    have := hn i
    change D i + b i ≤ n i at this
    omega
  have hnsub : D + (n - D) = n := by
    funext i
    exact Nat.add_sub_of_le (hDn i)
  have heval : eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
      eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    have hc : (fun i => ((n i : ℚ) - D i)) = (fun i => (((n - D) i : ℕ) : ℚ)) := by
      funext i
      simp [Nat.cast_sub (hDn i)]
    clear hb
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
        simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
        rw [congrFun hc i]
  rw [map_sub, heval, hb n hbn, hb (n - D) hbsub]
  have hdim := PhilipponMultiplicity.regular_hypersurface_hilbert_function K M I hI P D hP hregular (n - D)
  rw [hnsub] at hdim
  exact_mod_cast (show
    (hilbertFunction K M.factorCount M.ambientDimension I n : ℚ) -
      hilbertFunction K M.factorCount M.ambientDimension I (n - D) =
      hilbertFunction K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) n by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hdim
    push_cast at hcast
    linarith)


end PhilipponMultiplicity.Hilbert
end

-- Reused from Solutions/PhilipponHypersurfaceDegree.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree FiniteDifference

private def boundedExponent {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (α : BoundedMultiIndex M) : M.FactorIndex →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α i).val)

private theorem bounded_expansion {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (F : MvPolynomial M.FactorIndex ℚ)
    (hbound : ∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) → coeff b F = 0) :
    F = ∑ α : BoundedMultiIndex M, monomial (boundedExponent M α)
      (coeff (boundedExponent M α) F) := by
  classical
  ext b
  rw [coeff_sum]
  by_cases hb : ∀ i, b i ≤ M.ambientDimension i
  · let α : BoundedMultiIndex M := fun i => ⟨b i, Nat.lt_succ_of_le (hb i)⟩
    have hα : boundedExponent M α = b := by ext i; rfl
    rw [Finset.sum_eq_single α]
    · simp [hα]
    · intro β _ hβα
      have hne : boundedExponent M β ≠ b := by
        intro heq
        apply hβα
        funext i
        apply Fin.ext
        exact congrArg (fun e : M.FactorIndex →₀ ℕ => e i) heq
      simp [coeff_monomial, hne]
    · simp
  · have houtside : ∃ i, M.ambientDimension i < b i := by simpa using hb
    rw [hbound b houtside]
    symm
    apply Finset.sum_eq_zero
    intro α _
    have hne : boundedExponent M α ≠ b := by
      intro heq
      obtain ⟨i, hi⟩ := houtside
      have heqi := congrArg (fun e : M.FactorIndex →₀ ℕ => e i) heq
      change (α i).val = b i at heqi
      have := (α i).isLt
      omega
    simp [coeff_monomial, hne]

/-- The entire degree calculation of Lemma 3.1 follows from the genuine
Hilbert-polynomial existence and leading-coefficient facts. -/
theorem lemma_3_1_of_hilbert_data
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hexists : ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F)
    (hpositive : ∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)))
    (hbounded : ∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0)
    (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) :
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  classical
  let F := Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I
  let a := F.totalDegree
  let Q := F - shift (fun i => (D i : ℚ)) F
  have ha' : 0 < a := ha
  have hD' : ∀ i, (0 : ℚ) < D i := by
    intro i
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hD i))
  have hpoly : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P}) = Q :=
    Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial _ _ _ _
      (Hilbert.IsHilbertPolynomial.hypersurface M I hI P D hP hregular F
        (Hilbert.hilbertPolynomial_spec _ _ _ _ hexists))
  obtain ⟨hdegree, htop⟩ := difference_degree (fun i => (D i : ℚ)) hD' F ha' hpositive
  have hvalue (d : M.FactorIndex → ℕ) :
      idealDegreeValue M (I ⊔ Ideal.span {P}) d =
        ((a - 1).factorial : ℚ) *
          eval (fun i => (d i : ℚ)) (deriv (fun i => (D i : ℚ)) (homogeneousComponent a F)) := by
    unfold idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
    rw [hpoly]
    change eval _ ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) = _
    change Q.totalDegree = a - 1 at hdegree
    change homogeneousComponent Q.totalDegree Q =
      deriv (fun i => (D i : ℚ)) (homogeneousComponent a F) at htop
    rw [htop, hdegree, MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  constructor
  · intro d hd
    have hd' : ∀ i, (d i : ℚ) ≠ 0 := by
      intro i
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hd i)))
    rw [hvalue, bounded_expansion M (homogeneousComponent a F) hbounded,
      map_sum, map_sum, Finset.mul_sum]
    unfold hypersurfaceCoefficientSum
    apply Finset.sum_congr rfl
    intro α _
    rw [eval_deriv_monomial _ _ hd']
    have hsum : (boundedExponent M α).degree = ∑ i, (α i).val := by
      simp [Finsupp.degree_eq_sum, boundedExponent]
    rw [coeff_homogeneousComponent, hsum]
    change ((a - 1).factorial : ℚ) *
      ((if ∑ i, (α i).val = a then coeff (boundedExponent M α) F else 0) *
        (∑ i, ((α i).val : ℚ) * (D i : ℚ) / (d i : ℚ)) *
        ∏ i, (d i : ℚ) ^ (α i).val) =
        (if ∑ i, (α i).val = a then
          ((if ∑ i, (α i).val = a then
              coeff (boundedExponent M α) F * ∏ i, ((α i).val.factorial : ℚ) else 0) *
            ∑ i, ((α i).val : ℚ) * (D i : ℚ) / (d i : ℚ)) *
            ((a - 1).factorial : ℚ) / (∏ i, ((α i).val.factorial : ℚ)) *
            ∏ i, (d i : ℚ) ^ (α i).val else 0)
    by_cases hα : ∑ i, (α i).val = a
    · rw [if_pos hα, if_pos hα, if_pos hα]
      have hfac : (∏ i, ((α i).val.factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
      field_simp
    · simp only [if_neg hα, zero_mul, mul_zero]
  · rw [hvalue, eval_deriv_self _ _ _ (homogeneousComponent_isHomogeneous _ _)]
    change ((a - 1).factorial : ℚ) * ((a : ℚ) * eval _ (homogeneousComponent a F)) =
      eval _ ((a.factorial : ℚ) • homogeneousComponent a F)
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    change _ = (a.factorial : ℚ) * _
    have haeq : a = (a - 1) + 1 := by omega
    have hfac : ((a - 1).factorial : ℚ) * (a : ℚ) = (a.factorial : ℚ) := by
      have hh := Nat.factorial_succ (a - 1)
      rw [← haeq] at hh
      exact_mod_cast (Nat.mul_comm _ _).trans hh.symm
    rw [← mul_assoc, hfac]

end PhilipponMultiplicity

end

theorem solution
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hexists : ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F)
    (hpositive : ∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)))
    (hbounded : ∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0)
    (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) :
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  exact PhilipponMultiplicity.lemma_3_1_of_hilbert_data K M I hI hexists hpositive hbounded
    ha D hD P hP hregular
#print axioms solution
