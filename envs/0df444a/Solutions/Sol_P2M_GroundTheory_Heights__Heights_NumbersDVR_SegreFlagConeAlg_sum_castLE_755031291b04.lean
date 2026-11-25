-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:17:16.407645+00:00
-- url     : https://prove2.me/submissions/e86e9a93-7edc-478b-876a-d430142d45d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
theorem _root_.solution {M : Type*} [AddCommMonoid M] {N k : ℕ} (hkN : k ≤ N) (s : Fin N → M)
    (hs : ∀ j : Fin N, k ≤ (j : ℕ) → s j = 0) : ∑ j, s j = ∑ j : Fin k, s (Fin.castLE hkN j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hkN) (Fin.castLE_injective hkN) _ _ (fun j hj => hs j ?_)
    (fun _ => rfl)
  by_contra h
  exact hj ⟨⟨j, by omega⟩, Fin.ext rfl⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg
