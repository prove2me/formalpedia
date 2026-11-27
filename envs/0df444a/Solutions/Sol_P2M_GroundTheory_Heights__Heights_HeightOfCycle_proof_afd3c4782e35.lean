-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightOfCycle_proof_afd3c4782e35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:50.580955+00:00
-- url     : https://prove2.me/submissions/d4316958-6278-46cc-90a9-3a5d9da5628e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_map_49e491896c3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_finsum_log_gaussNorm_prod_bff67275f7cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_adicAbv_f04fbb456bfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_embeddings_restrict_5832e9921bd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_log_norm_embeddings_2fdebfa8404c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
open HeightOfCycle
namespace GroundTheory.Heights₂.Heights
namespace HeightOfCycle
theorem _root_.solution (h1 : HeightOfPoint.Statement) (h2 : FibreMahlerForms.Statement) :
    HeightOfCycle.Statement := by
  intro F _ _ W _ _ _ _ h n w hw E _ _ _ K _ _ _ _ _ m yv hyv c hc P hP

  have hL : ∀ q, (∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 := by
    intro q h0
    apply hyv q
    have hle : Submodule.span (𝓞 F) (Set.range w) ≤ LinearMap.ker (yv q) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := congrArg (coeff (Finsupp.single k 1)) h0
      simp only [coeff_sum, coeff_C_mul, coeff_X, coeff_zero] at this
      rw [Finset.sum_eq_single k (fun j _ hj ↦ by
        rw [if_neg (fun e ↦ hj (Finsupp.single_left_injective one_ne_zero e)), mul_zero])
        (by simp)] at this
      simpa using this
    rw [hw, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle
  have hprod : (∏ q, ∑ k, C (yv q (w k)) * X k : MvPolynomial (Fin n) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc) hprod hP.symm
  have hr : (Module.finrank E K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

  have hpt : ∀ q, pointHeight h (yv q) = (Module.finrank ℚ K : ℝ)⁻¹ *
      ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) +
        ∑ τ : K →+* ℂ, Real.log (archDualNorm h τ (yv q))) := by
    intro q
    obtain ⟨hloc, hht⟩ := h1 F W h n w hw K (yv q) (hyv q)
    have hex : ∃ x, yv q x ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hyv q (LinearMap.ext hne)
    rw [pointHeight, hht _ (Classical.epsilon_spec hex)]
    congr 2
    exact finsum_congr fun v ↦ by rw [(hloc v).2]

  have hfin : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Real.log (gaussNorm v P) =
      (Module.finrank E K : ℝ)⁻¹ *
        ((∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (NumberField.HeightOneSpectrum.adicAbv K v c)) +
          ∑ q, ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            Real.log (gaussNorm v (∑ k, C (yv q (w k)) * X k))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← finsum_log_gaussNorm_map hPne, hP,
      finsum_log_gaussNorm_mul (C_ne_zero.mpr hc) hprod,
      finsum_log_gaussNorm_prod Finset.univ (fun q ↦ ∑ k, C (yv q (w k)) * X k) hL]
    simp_rw [gaussNorm_C]

  have harch : ∑ σ : E →+* ℂ, (fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2) =
      (Module.finrank E K : ℝ)⁻¹ * ∑ τ : K →+* ℂ,
        (Real.log ‖τ c‖ + ∑ q, Real.log (archDualNorm h τ (yv q))) := by
    rw [eq_inv_mul_iff_mul_eq₀ hr, ← sum_embeddings_restrict (K := E) (L := K)
      (fun σ : E →+* ℂ ↦ fibreMahler h (σ.comp (algebraMap F E)) w (P.map σ) +
        m * (harmonic (Module.finrank (𝓞 F) W - 1) : ℝ) / 2)]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    have e1 : (τ.comp (algebraMap E K)).comp (algebraMap F E) = τ.comp (algebraMap F K) := by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    have e2 : P.map (τ.comp (algebraMap E K)) =
        C (τ c) * ∏ q, ∑ k, C (τ (yv q (w k))) * X k := by
      rw [← MvPolynomial.map_map, hP]
      simp only [map_mul, map_prod, map_sum, map_C, map_X]
    rw [e1, e2, h2 F W h n w hw K τ m yv hyv (τ c) ((map_ne_zero τ).mpr hc)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hfin, harch, Finset.sum_add_distrib, finsum_log_adicAbv hc, sum_log_norm_embeddings hc,
    Finset.sum_comm (f := fun τ q ↦ Real.log (archDualNorm h τ (yv q)))]
  simp_rw [hpt]
  rw [← Module.finrank_mul_finrank ℚ E K, ← Finset.mul_sum, Finset.sum_add_distrib]
  push_cast
  field_simp
  ring
end HeightOfCycle
end GroundTheory.Heights₂.Heights
