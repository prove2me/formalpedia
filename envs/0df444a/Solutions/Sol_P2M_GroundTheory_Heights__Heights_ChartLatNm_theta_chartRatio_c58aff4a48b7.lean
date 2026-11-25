-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:43.780309+00:00
-- url     : https://prove2.me/submissions/8ed93caa-96fe-4bad-9ed2-9d22be7bfe0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c c' : (k : ι) → Fin (n k + 1)) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (e : ι → ℤ) :
    theta P y hP hb ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c' k⟩ ^ (-e k)) =
      P.chartPow c e / P.chartPow c' e := by
  rw [← Finset.prod_mul_distrib, map_prod, ArithVariety.chartPow, ArithVariety.chartPow,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_neg, ← div_eq_mul_inv, ← div_zpow, map_zpow₀, ← div_zpow]
  congr 1
  exact theta_eq P y hP hb (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩)
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c' k⟩ :
      IsWeightedHomogeneous _ _ (coordDeg n ⟨k, c k⟩))
    (by rw [aeval_X]; exact hc' k) (by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (hc' k)])
end GroundTheory.Heights₂.Heights.ChartLatNm
