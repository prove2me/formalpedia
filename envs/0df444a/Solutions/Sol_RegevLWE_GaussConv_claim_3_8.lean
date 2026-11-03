-- Prove2me | solution 1 for RegevLWE.GaussConv.claim_3_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:54:48.56003+00:00
-- url     : https://prove2.me/submissions/af5fdaee-0827-49ca-bf1d-17b91a8b493a

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark

open MeasureTheory Filter Topology FourierTransform RegevLWE.GaussConv
open scoped FourierTransform SchwartzMap

set_option backward.isDefEq.respectTransparency.types false

private lemma inner_nondegenerate (n : ℕ) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun x hx => inner_self_eq_zero.mp (hx x)⟩

private lemma inner_flip_eq (n : ℕ) :
    LinearMap.BilinForm.flip (innerₗ (EuclideanSpace ℝ (Fin n))) =
      innerₗ (EuclideanSpace ℝ (Fin n)) := by
  ext x y
  exact real_inner_comm x y

private lemma exists_schwartz_rho (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x : EuclideanSpace ℝ (Fin n),
      f x = (rho r x : ℂ) := by
  obtain ⟨g, hg⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin n)
  let u : ℝˣ := Units.mk0 r⁻¹ (inv_ne_zero hr.ne')
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft u
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e g, fun x => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg, rho]
  congr 2
  have he : e x = r⁻¹ • x := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  ring

private lemma fourier_schwartz_rho {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hf : ∀ x, f x = (rho r x : ℂ))
    (w : EuclideanSpace ℝ (Fin n)) :
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
      (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) w =
      (r : ℂ) ^ n * (rho (1 / r) w : ℂ) := by
  have hfn : (⇑f : EuclideanSpace ℝ (Fin n) → ℂ) = fun x => (rhoShift r 0 x : ℂ) := by
    funext x
    rw [hf x]
    simp [rhoShift]
  have h_four := RegevLWE.GaussConv.fourier_rhoShift hr (0 : EuclideanSpace ℝ (Fin n)) w
  change VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (rhoShift r 0 x : ℂ)) w = _ at h_four
  rw [hfn, h_four]
  simp [inner_zero_left]

private lemma rhoDualNonzero_le_of_smoothingParam_le {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (h : smoothingParam L ε ≤ r) :
    rhoDualNonzero (1 / r) L ≤ ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {y : dual L // y ≠ 0} := ⟨fun ⟨y, hy⟩ => hy (Subsingleton.elim y 0)⟩
    unfold rhoDualNonzero
    simp [hε.le]
  · obtain ⟨_, hanti, _, _, hsp⟩ := RegevLWE.GaussConv.smoothing_remark hn L
    obtain ⟨hsp_pos, hsp_eq⟩ := hsp ε hε
    rw [← hsp_eq]
    exact hanti.antitoneOn hsp_pos hr h

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (c : EuclideanSpace ℝ (Fin n)) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (h : smoothingParam L ε ≤ r) :
    |rhoCoset r L c - r ^ n * (ZLattice.covolume L)⁻¹| ≤
      ε * (r ^ n * (ZLattice.covolume L)⁻¹) := by
  obtain ⟨f, hf⟩ := exists_schwartz_rho n hr
  have h_poisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) L f c
  have h_sum := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n) L f c
  rw [inner_flip_eq n] at h_poisson h_sum
  set term : dual L → ℂ := fun y =>
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f)
      (y : EuclideanSpace ℝ (Fin n)) *
      (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) c (y : EuclideanSpace ℝ (Fin n))) : ℂ)
  change ∑' x : L, f (c + (x : EuclideanSpace ℝ (Fin n))) =
    (ZLattice.covolume L MeasureTheory.volume : ℂ)⁻¹ * ∑' y : dual L, term y at h_poisson
  change Summable term at h_sum
  have h_lhs : (∑' x : L, f (c + (x : EuclideanSpace ℝ (Fin n)))) = (rhoCoset r L c : ℂ) := by
    unfold rhoCoset
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [hf, add_comm c]
  have h_compl : ({0} : Set (dual L))ᶜ = {y : dual L | y ≠ 0} := by
    ext y
    simp
  have h_split := (h_sum.tsum_subtype_add_tsum_subtype_compl ({0} : Set (dual L))).symm
  rw [tsum_singleton 0 term, h_compl] at h_split
  change ∑' y : dual L, term y = term 0 + ∑' y : {y : dual L // y ≠ 0}, term y.1 at h_split
  rw [h_lhs, h_split] at h_poisson
  have h_zero : term 0 = (r : ℂ) ^ n := by
    dsimp [term]
    rw [fourier_schwartz_rho hr f hf]
    simp [rho]
  rw [h_zero, mul_add] at h_poisson
  have h_sub : ((rhoCoset r L c - r ^ n * (ZLattice.covolume L)⁻¹ : ℝ) : ℂ) =
      (ZLattice.covolume L : ℂ)⁻¹ *
        ∑' y : {y : dual L // y ≠ 0}, term y.1 := by
    push_cast
    rw [h_poisson]
    ring
  have h_cov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
  have h_norm_eq := congrArg norm h_sub
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg h_cov_pos.le] at h_norm_eq
  have h_term_norm : ∀ y : {y : dual L // y ≠ 0},
      ‖term y.1‖ = r ^ n * rho (1 / r) (y.1 : EuclideanSpace ℝ (Fin n)) := by
    intro y
    dsimp [term]
    rw [fourier_schwartz_rho hr f hf, norm_mul, norm_mul, Circle.norm_coe, mul_one,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Complex.norm_real, Real.norm_of_nonneg (by unfold rho; positivity)]
  have h_sum_sub := (h_sum.subtype {y : dual L | y ≠ 0}).norm
  have h_tsum_le : ‖∑' y : {y : dual L // y ≠ 0}, term y.1‖ ≤
      r ^ n * rhoDualNonzero (1 / r) L := by
    calc ‖∑' y : {y : dual L // y ≠ 0}, term y.1‖
        ≤ ∑' y : {y : dual L // y ≠ 0}, ‖term y.1‖ :=
          norm_tsum_le_tsum_norm h_sum_sub
      _ = ∑' y : {y : dual L // y ≠ 0}, (r ^ n * rho (1 / r) (y.1 : EuclideanSpace ℝ (Fin n))) := by
           simp_rw [h_term_norm]
      _ = r ^ n * rhoDualNonzero (1 / r) L := by
          rw [tsum_mul_left]
          rfl
  have h_sp_le := rhoDualNonzero_le_of_smoothingParam_le L hε hr h
  rw [h_norm_eq]
  calc (ZLattice.covolume L)⁻¹ * ‖∑' y : {y : dual L // y ≠ 0}, term y.1‖
      ≤ (ZLattice.covolume L)⁻¹ * (r ^ n * rhoDualNonzero (1 / r) L) :=
        mul_le_mul_of_nonneg_left h_tsum_le (inv_nonneg.mpr h_cov_pos.le)
    _ ≤ (ZLattice.covolume L)⁻¹ * (r ^ n * ε) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_sp_le (pow_nonneg hr.le n))
          (inv_nonneg.mpr h_cov_pos.le)
    _ = ε * (r ^ n * (ZLattice.covolume L)⁻¹) := by ring
