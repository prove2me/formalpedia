-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:29.953769+00:00
-- url     : https://prove2.me/submissions/c9a5a7af-baa3-4fff-adad-cc921d5f1ead

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZChartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_left_2c27ecd7d652


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
open AmpleAffineGen AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
theorem _root_.solution (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by
  obtain ⟨a, ha, hay⟩ := (G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy
  obtain ⟨w, hw⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I K w.2
  refine ⟨D, ?_⟩
  have hw' : (w : Ω) * (a : Ω) = 1 := congrArg Subtype.val hw
  have e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    change _ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)
    rw [smul_smul, mul_assoc, hw', mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ hay
end GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
