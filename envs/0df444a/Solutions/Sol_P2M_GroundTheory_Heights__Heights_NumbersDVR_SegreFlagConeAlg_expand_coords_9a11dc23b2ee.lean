-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_expand_coords_9a11dc23b2ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:14.674843+00:00
-- url     : https://prove2.me/submissions/3716778e-5fae-4cd9-bbff-77e22dc04595

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {n : ℕ} {σ : Type*} (u : Fin n → E) (s' : Fin n → Φ) (ψ : Module.Dual Ω E) (V : Φ)
    (hV : V = ∑ q, s' q * algebraMap Ω Φ (ψ (u q))) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) * (C (algebraMap Ω Φ Y * s' q) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * V) * X o := by
  rw [hV, Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  simp only [map_div₀]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
