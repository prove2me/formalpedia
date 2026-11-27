-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_metric_b6d4d757a33f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:34.942511+00:00
-- url     : https://prove2.me/submissions/cd454889-df67-4b72-9e91-8d1a1c3dff34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_twistPow_eq_3efc6f400acc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (M : HermLine n) (p a : ℕ) (C : ℝ) (z : Cone n ℂ) :
    (twistPow M p a C).metric z =
      Real.exp (-(a * C)) * (((M.pow p).mul (HermLine.standard n)).pow a).metric z := by
  rw [twistPow_eq]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
