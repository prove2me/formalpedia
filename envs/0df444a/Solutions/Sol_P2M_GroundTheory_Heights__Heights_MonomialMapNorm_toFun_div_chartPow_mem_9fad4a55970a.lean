-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_div_chartPow_mem_9fad4a55970a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:35.310473+00:00
-- url     : https://prove2.me/submissions/afd74f0b-8cb9-4fa8-8493-6b9f4f318b55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_ne_zero_514ac748f9fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_chartPow_add_67d12914ee42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_form_div_mem_df5c07c6a0e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_mkF_chartForm_c55ff95110ec

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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {a : ι → ℤ} (s : IntegralSection P a) {c : (k : ι) → Fin (n k + 1)}
    (hc : P.IsLive c) : s.toFun / P.chartPow c a ∈ P.chartRing c := by
  obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hc
  have hmk := mkF_chartForm P s ⟨⟨δ, he, hδ⟩, hmem⟩
  have hM : P.mkF (chartMonomial c d) = P.chartPow c (fun k ↦ (d k : ℤ)) := by
    simp only [chartMonomial, map_prod, map_pow, ArithVariety.chartPow, zpow_natCast]
  have hδ' : (fun k ↦ (δ k : ℤ)) = a + fun k ↦ (d k : ℤ) := funext fun k ↦ hδ k
  have key : s.toFun / P.chartPow c a = P.mkF e / P.chartPow c (fun k ↦ (δ k : ℤ)) := by
    rw [hδ', chartPow_add P hc, hmk, hM, mul_div_mul_right _ _ (chartPow_ne_zero P hc _)]
  rw [key]
  exact form_div_mem P hc he
end GroundTheory.Heights₂.Heights.MonomialMapNorm
