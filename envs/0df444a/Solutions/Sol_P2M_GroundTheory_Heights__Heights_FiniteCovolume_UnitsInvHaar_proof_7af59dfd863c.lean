-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnitsInvHaar_proof_7af59dfd863c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:41.525992+00:00
-- url     : https://prove2.me/submissions/dca737ac-1787-46a2-87e8-65e8ad0ffbdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnitsInvHaar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnitsInvHaar_measurable_units_val_52add3eb92ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnitsInvHaar_invHaar_ne_zero_515dd67bac35

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Measure Set
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
variable {I : Type*} [Fintype I]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
theorem _root_.solution (I : Type*) [Fintype I] : UnitsInvHaar.Statement I := by
  intro ρ _
  have hlam := isMulLeftInvariant_eq_smul (invHaar I) ρ
  set c' := haarScalarFactor (invHaar I) ρ
  have hc' : c' ≠ 0 := by
    intro h
    apply invHaar_ne_zero (I := I)
    rw [hlam, h, zero_smul]
  refine ⟨c'⁻¹, inv_ne_zero hc', fun k g g' hg hg' => ?_⟩
  have hρ : ρ = (c'⁻¹ : ℝ≥0) • invHaar I := by
    rw [hlam, smul_smul, inv_mul_cancel₀ hc', one_smul]
  have hF : Measurable fun a : I → ℂˣ => (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a :=
    (Finset.measurable_prod _ fun i _ =>
      ((measurable_units_val.comp (measurable_pi_apply i)).enorm.inv).pow_const _).mul hg
  rw [hρ, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [invHaar, lintegral_map hF measurable_invUnits, weightedVolume,
    lintegral_withDensity_eq_lintegral_mul _ measurable_invSqWeight
      (g := fun b => (∏ i, ‖(invUnits b i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g (invUnits b))
      (hF.comp measurable_invUnits)]
  apply lintegral_congr_ae
  filter_upwards [ae_ne_zero] with b hb
  have hinv : invUnits b = fun i => (Units.mk0 (b i) (hb i))⁻¹ := by
    funext i; simp [invUnits, hb i]
  simp only [Pi.mul_apply]
  rw [hinv, ← hg' b hb, ← mul_assoc]
  congr 1
  rw [invSqWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : ‖b i‖ₑ ≠ 0 := enorm_ne_zero.2 (hb i)
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, enorm_inv (hb i), inv_inv,
    show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, ← mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel h0 enorm_ne_top, one_pow, one_mul]
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
