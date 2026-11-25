-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_reads_readElt_97ddeb3ac6cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:25.199351+00:00
-- url     : https://prove2.me/submissions/117fe3dc-87ff-452a-ad43-0f421ec5b782

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_ne_zero_4863382afcb9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37

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
theorem _root_.solution (c₀ : (k : ι) → Fin (n k + 1)) (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    P.Reads y b s (readElt P y hP hb c₀ b s) := by
  intro g q δg δq hg hq hd
  have hG : (fun k => (δg k : ℤ)) = b + fun k => (δq k : ℤ) := by
    funext k
    rw [Pi.add_apply, hd k, add_comm]
  have hY : (∏ k, y ⟨k, c₀ k⟩ ^ (-(δg k : ℤ))) =
      (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc₀ k)]
    congr 1
    rw [hd k]
    ring
  have hY0 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (-(δq k : ℤ)) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k))
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc₀ k))
  rw [mkF_eq_theta P y hP hb c₀ hc₀ hg, mkF_eq_theta P y hP hb c₀ hc₀ hq, hG,
    chartPow_add P y hP c₀ hc₀, readElt,
    show ∀ u v w z : P.FunField, u * w * (v * z) = (u * v) * (w * z) from fun u v w z => by ring,
    ← map_mul, mul_left_inj' (mul_ne_zero (chartPow_ne_zero P y hP c₀ hc₀ _)
      (chartPow_ne_zero P y hP c₀ hc₀ _)), (theta P y hP hb).injective.eq_iff, hY]
  constructor
  · intro e
    rw [e]
    ring
  · intro e
    apply mul_right_cancel₀ hY0
    linear_combination e
end GroundTheory.Heights₂.Heights.ChartLatNm
