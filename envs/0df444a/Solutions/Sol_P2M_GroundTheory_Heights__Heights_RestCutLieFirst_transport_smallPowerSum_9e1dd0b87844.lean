-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:36.83507+00:00
-- url     : https://prove2.me/submissions/9d3a6cd0-d143-46bd-a19c-7dab699d890e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieFirst

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestCutLieFirst
namespace GroundTheory.Heights₂.Heights.RestCutLieFirst
theorem _root_.solution (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallPowerSum f j k .first m τ) =
      (-1) ^ m * ∑ a : Fin j, (X (τ, Sum.inl a) : RootPoly f j k) ^ m := by
  rw [Finset.mul_sum]
  simp only [RestTerms.smallPowerSum, map_sum, map_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidx : (restFirstEquiv j k) (⟨a.val, by omega⟩ : Fin (j + k)) = Sum.inl a := by
    have : (⟨a.val, by omega⟩ : Fin (j + k)) = Fin.castAdd k a := rfl
    rw [this, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, restTransport,
    restRename, RingHom.comp_apply, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_X, rename_C, hidx]
  rw [mul_pow]
  congr 1
  simp
end GroundTheory.Heights₂.Heights.RestCutLieFirst
