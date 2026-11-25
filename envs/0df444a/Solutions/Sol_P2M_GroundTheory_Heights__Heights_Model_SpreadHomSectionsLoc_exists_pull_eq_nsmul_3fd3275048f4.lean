-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_pull_eq_nsmul_3fd3275048f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:07.413097+00:00
-- url     : https://prove2.me/submissions/d8865f0c-caaf-4a29-86a3-e6bd7745d37c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
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
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
variable {Y T : Scheme.{0}} (π : T ⟶ Y) (p : ℕ)
namespace GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
theorem _root_.solution (hp : p.Prime) (h₂ : PullbackBasis.Statement.{0}) {W : Y.Opens}
    (hden : ∀ b : Γ(T, π ⁻¹ᵁ W), ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ c : Γ(Y, W), π.app W c = N • b)
    {G : Y.Modules} {k : ℕ} {e : Fin k → Γ(G, W)} (he : IsBasisOn G W e)
    (σ : Γ((Scheme.Modules.pullback π).obj G, π ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∃ τ : Γ(G, W), pullSectionOn π G W τ = N • σ := by
  have hb := (h₂ _ _ π G W k e he).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN hpN c hc using fun i => hden (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun h => ?_,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • c i) • e i, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.1 h
    exact hpN i hi
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, hc i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]
end GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc
