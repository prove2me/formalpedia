-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_readElt_div_2c67889bc5b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:54.753506+00:00
-- url     : https://prove2.me/submissions/f29b17f0-c265-4dda-85a7-3e17fb18c2b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_theta_chartRatio_c58aff4a48b7

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
theorem _root_.solution (c₀ c : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    readElt P y hP hb c₀ b s / P.chartPow c b = theta P y hP hb (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) := by
  rw [readElt, mul_div_assoc, ← theta_chartRatio P y hP hb c₀ c hc b, ← map_mul]
  congr 1
  have h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hc₀ k))]
  linear_combination (s * ∏ k, y ⟨k, c k⟩ ^ (-b k)) * h1
end GroundTheory.Heights₂.Heights.ChartLatNm
