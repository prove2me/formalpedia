-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:14.024299+00:00
-- url     : https://prove2.me/submissions/4ddef4af-8b8a-4c03-9c73-a3ff84e85b0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_pow_ca35e761ba25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_chartMonomial_ne_zero_f3bbdf95a0d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c

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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution (A : HermLine n) (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C)
    (m : ℕ) : IntegralSection.SupNormLE (A.pow m) (s.pow m) (m * C) := by
  intro z hz c d e he hc
  have live := live_of_point hz hc
  obtain ⟨d₁, e₁, he₁⟩ := s.regular c live
  have hmem : s.den ^ m * e₁ ^ m - s.num ^ m * chartMonomial c (m • d₁) ∈ P.ideal := by
    rw [chartMonomial_nsmul, ← mul_pow, ← mul_pow]
    exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ m) he₁.2
  have hv := chart_value_eq (s.pow m).den_not_mem he.2 hmem hz
  have hA := hs z hz c d₁ e₁ he₁ hc
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z ^ m) ≤ _
  rw [ratio_norm_eq (evalCone_chartMonomial_ne_zero z c d hc)
    (evalCone_chartMonomial_ne_zero z c _ hc) hv, evalCone_pow, chartMonomial_nsmul, evalCone_pow,
    norm_pow, norm_pow, ← mul_pow, ← div_pow, mul_comm (m : ℝ) C, Real.exp_mul, Real.rpow_natCast]
  exact pow_le_pow_left₀
    (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (A.metric_pos z hz.1).le)) hA m
end GroundTheory.Heights₂.Heights.MonomialMap
