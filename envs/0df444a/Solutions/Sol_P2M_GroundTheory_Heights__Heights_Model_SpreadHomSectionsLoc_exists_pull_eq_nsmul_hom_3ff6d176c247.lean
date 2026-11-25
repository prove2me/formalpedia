-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_hom_3ff6d176c247
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:59.048775+00:00
-- url     : https://prove2.me/submissions/56874921-b989-4cb4-9439-122d0e905c84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4
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
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
variable {Y T : Scheme.{0}} (π : T ⟶ Y) (p : ℕ)
namespace GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
theorem _root_.solution (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {F G : Y.Modules} (φ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, W)} {e' : Fin k' → Γ(G, W)}
    (he : IsBasisOn F W e) (he' : IsBasisOn G W e') :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∀ V : Y.Opens, V ≤ W → ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
      pullSectionOn π G V τ = N • φ.app (π ⁻¹ᵁ V) (pullSectionOn π F V s) := by
  classical
  choose N hN hpN τ hτ using fun i => exists_pull_eq_nsmul π p hp h₂ hden he'
    (φ.app _ (pullSectionOn π F _ (e i)))
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun h => ?_, fun V hV s => ?_⟩
  · obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 h
    exact hpN i hi
  obtain ⟨r, rfl⟩ := (he V hV).2 s
  refine ⟨∑ i, r i • (G.presheaf.map (homOfLE hV).op).hom ((∏ j ∈ Finset.univ.erase i, N j) • τ i), ?_⟩
  have hV' : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ W := (Opens.map π.base).monotone hV
  rw [pullSectionOn_sum, pullSectionOn_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, smul_comm]
  congr 1
  rw [pullSectionOn_res _ _ hV (homOfLE hV'), pullSectionOn_res _ _ hV (homOfLE hV'), map_nsmul, hτ,
    smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), app_map_apply, map_nsmul]
end GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
