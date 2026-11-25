-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:59.965186+00:00
-- url     : https://prove2.me/submissions/9467877f-afb0-4c37-9396-98b505d2a06a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsRatDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_app_eq_nsmul_3f3952484f35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9


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
theorem _root_.solution (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    {U : X.Opens} (hU : IsAffineOpen U) {G : (invOpen f a : Scheme.{0}).Modules} {k : ℕ}
    {e : Fin k → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)} (he : IsBasisOn G _ e)
    (σ : Γ((Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G,
      toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(G, (invOpen f a).ι ⁻¹ᵁ U),
      pullSectionOn (toInvOpen f ℚ a hq) G _ τ = N • σ := by
  have hb := (h₂ _ _ (toInvOpen f ℚ a hq) G _ k e he).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN c hc using fun i => exists_app_eq_nsmul f a hq h₁ hU (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • c i) • e i, ?_⟩
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, hc i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]
end GroundTheory.Heights₂.Heights.Model.SpreadHomSections
