-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometricEventOrder_priority
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:53:07.486209+00:00
-- url     : https://prove2.me/submissions/ee168b98-e3b5-4c13-8e76-e2a6c2b1ae24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (geometricEventOrder P J r).toLE.le e f ↔ eventPriorityLE P J r e f := Iff.rfl
end QEC.Coding.BDL26RandomPerturbation
