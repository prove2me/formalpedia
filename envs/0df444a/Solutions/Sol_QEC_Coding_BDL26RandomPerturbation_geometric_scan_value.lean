-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometric_scan_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:53:24.314688+00:00
-- url     : https://prove2.me/submissions/8843943f-841f-4414-a79e-1f40224e1685

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_scanQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (p : Vertex P → Space) :
    (scanQuery (geometricGlobalQuery P J r lambda K)
      ((Finset.univ : Finset (Event P J r)).sort (eventPriorityLE P J r)) p).1 =
      select (localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K)) p :=
  scanQuery_value _ _ (geometricGlobalQuery_correct P J r lambda K) _ p
end QEC.Coding.BDL26RandomPerturbation
