-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_isLive_iff__2b823a4f59be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:50.588872+00:00
-- url     : https://prove2.me/submissions/b5f76229-a575-4c64-966e-d13d29a99ba0

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
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1)) :
    P.IsLive c ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  rw [hP, mem_mCoordIdeal_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩), aeval_X]
end GroundTheory.Heights₂.Heights.ChartLatNm
