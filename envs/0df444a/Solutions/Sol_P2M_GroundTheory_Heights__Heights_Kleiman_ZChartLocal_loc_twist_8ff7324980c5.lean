-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_twist_8ff7324980c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:19.854006+00:00
-- url     : https://prove2.me/submissions/bedfca13-2050-47e0-8e5a-e02f9a2dffa2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZChartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_ratio_pow_smul_mem_d4d51a04cb02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_loc_subFamily_a3f50380ed45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_of_eq_45744a7bcb93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041


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
theorem _root_.solution (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction (p := fun y _ => ∃ c : ℕ,
    chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, z, hz, rfl⟩
    obtain ⟨D₁, h₁⟩ := exists_pow_mul_mem_of_eq (H.powBundle q)
      (LineBundle.powBundle_toSubSystem H q) I K hp
    obtain ⟨D₂, h₂⟩ := loc_subFamily G I K hz
    refine ⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    have e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) =
        chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]
    rw [e]
    exact Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)
  · rintro a y - ⟨c, hc⟩
    obtain ⟨D, hD⟩ := exists_pow_mul_mem I K a.2
    refine ⟨D + c, ?_⟩
    have e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y) := by
      change chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)
      rw [smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hc
end GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
