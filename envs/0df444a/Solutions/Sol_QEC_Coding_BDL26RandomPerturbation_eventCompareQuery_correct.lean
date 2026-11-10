-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventCompareQuery_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:55:17.613019+00:00
-- url     : https://prove2.me/submissions/8e6f702b-4717-4f4d-9c7e-bf50c5712bf6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lexLEQuery_correct
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventKeyQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) :
    (eventCompareQuery P J radius e f).1 = true ↔
      eventScanKey P J radius e ≤ eventScanKey P J radius f := by
  rw [eventCompareQuery,lexLEQuery_correct,eventKeyQuery_value,eventKeyQuery_value]
end QEC.Coding.BDL26RandomPerturbation
