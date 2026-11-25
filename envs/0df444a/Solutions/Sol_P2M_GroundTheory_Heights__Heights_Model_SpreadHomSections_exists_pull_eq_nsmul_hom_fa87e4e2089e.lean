-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_hom_fa87e4e2089e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:00.511795+00:00
-- url     : https://prove2.me/submissions/be3df0a5-682b-4c68-8bb8-b68c00684855

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsRatDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSections_exists_pull_eq_nsmul_8f51e6cf42cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
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
    {U : X.Opens} (hU : IsAffineOpen U) {F G : (invOpen f a : Scheme.{0}).Modules}
    (φ : (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, (invOpen f a).ι ⁻¹ᵁ U)} {e' : Fin k' → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)}
    (he : IsBasisOn F _ e) (he' : IsBasisOn G _ e') :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U →
      ∀ s : Γ(F, V), ∃ τ : Γ(G, V), pullSectionOn (toInvOpen f ℚ a hq) G V τ =
        N • φ.app (toInvOpen f ℚ a hq ⁻¹ᵁ V) (pullSectionOn (toInvOpen f ℚ a hq) F V s) := by
  classical
  choose N hN τ hτ using fun i => exists_pull_eq_nsmul f a hq h₁ h₂ hU he'
    (φ.app _ (pullSectionOn (toInvOpen f ℚ a hq) F _ (e i)))
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun V hV s => ?_⟩
  obtain ⟨r, rfl⟩ := (he V hV).2 s
  refine ⟨∑ i, r i • (G.presheaf.map (homOfLE hV).op).hom ((∏ j ∈ Finset.univ.erase i, N j) • τ i), ?_⟩
  have hV' : toInvOpen f ℚ a hq ⁻¹ᵁ V ≤ toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U) :=
    (Opens.map (toInvOpen f ℚ a hq).base).monotone hV
  rw [pullSectionOn_sum, pullSectionOn_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, smul_comm]
  congr 1
  rw [pullSectionOn_res _ _ hV (homOfLE hV'), pullSectionOn_res _ _ hV (homOfLE hV'), map_nsmul, hτ,
    smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), app_map_apply, map_nsmul]
end GroundTheory.Heights₂.Heights.Model.SpreadHomSections
