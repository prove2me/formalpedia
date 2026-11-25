-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:09.280338+00:00
-- url     : https://prove2.me/submissions/c5d40f4c-dd79-47ef-ad78-7f70f3148d3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsRatDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.SpreadHomSections
variable {X : Scheme.{0}} (f : X ⟶ SpecZ) (a : ℤ) (hq : IsUnit (a : ℚ))
namespace GroundTheory.Heights₂.Heights.Model.SpreadHomSections
theorem _root_.solution (h₁ : RatDenominators.Statement) {U : X.Opens} (hU : IsAffineOpen U)
    (b : Γ(baseChange f ℚ, toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : Γ((invOpen f a : Scheme.{0}), (invOpen f a).ι ⁻¹ᵁ U),
      (toInvOpen f ℚ a hq).app _ c = N • b := by
  have h := h₁ X f U hU
  rw [← toInvOpen_ι f ℚ a hq] at h
  obtain ⟨N, hN, c, hc⟩ := h b
  exact ⟨N, hN, (invOpen f a).ι.app U c, hc⟩
end GroundTheory.Heights₂.Heights.Model.SpreadHomSections
