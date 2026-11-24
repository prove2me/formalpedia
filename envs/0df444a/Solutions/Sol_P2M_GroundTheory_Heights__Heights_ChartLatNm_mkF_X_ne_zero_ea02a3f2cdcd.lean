-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_X_ne_zero_ea02a3f2cdcd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:57.842903+00:00
-- url     : https://prove2.me/submissions/2a780bd7-4dbe-4592-b3a6-a388215d51cd

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
theorem _root_.solution (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : ι) : P.mkF (X ⟨k, c k⟩) ≠ 0 := fun h =>
  hc k (by
    rw [← aeval_X (R := ℤ) y ⟨k, c k⟩]
    exact (mkF_eq_zero_iff' P y hP (isWeightedHomogeneous_X ℤ (coordDeg n) _)).mp h)
end GroundTheory.Heights₂.Heights.ChartLatNm
