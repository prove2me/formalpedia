-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_chartPow_add_5b9372cef19a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:32.264277+00:00
-- url     : https://prove2.me/submissions/ed594b09-71aa-45f1-aed4-fe663e16ac46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd

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
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e e' : ι → ℤ) :
    P.chartPow c (e + e') = P.chartPow c e * P.chartPow c e' := by
  simp only [ArithVariety.chartPow, Pi.add_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (mkF_X_ne_zero P y hP c hc k) _ _
end GroundTheory.Heights₂.Heights.ChartLatNm
