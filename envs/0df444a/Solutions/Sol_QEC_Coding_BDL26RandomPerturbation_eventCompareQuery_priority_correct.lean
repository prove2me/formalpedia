-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_priority_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:49:35.361347+00:00
-- url     : https://prove2.me/submissions/3c0afe10-ecb5-466d-9bf5-685712c8fda3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibleListQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedTuples
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventCompareQuery_correct


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : (eventCompareQuery P J r e f).1 = true ↔ eventPriorityLE P J r e f :=
  eventCompareQuery_correct P J r e f
end QEC.Coding.BDL26RandomPerturbation
