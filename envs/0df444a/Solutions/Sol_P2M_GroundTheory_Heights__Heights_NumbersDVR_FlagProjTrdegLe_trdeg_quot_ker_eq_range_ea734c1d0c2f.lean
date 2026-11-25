-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagProjTrdegLe_trdeg_quot_ker_eq_range_ea734c1d0c2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:09.584406+00:00
-- url     : https://prove2.me/submissions/e78b9602-0965-4344-a97c-eafbe608af89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
theorem _root_.solution {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (hg : Function.Injective g) :
    Algebra.trdeg R (A ⧸ RingHom.ker f) = Algebra.trdeg R (g.comp f).range := by
  have hker : RingHom.ker (g.comp f) = RingHom.ker f := by
    ext a
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    exact ⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  rw [← hker]
  exact (Ideal.quotientKerEquivRange (g.comp f)).trdeg_eq
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagProjTrdegLe
