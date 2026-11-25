-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_pointIdeal_a7cacdac11cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:21.173067+00:00
-- url     : https://prove2.me/submissions/4dbaa1a0-3d5c-4c66-b42a-28bfe71ba6b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagProjSpecialDim
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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by
  ext a
  simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
    MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]
  exact ⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
