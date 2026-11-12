-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventToMaster_priority
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:08:52.074037+00:00
-- url     : https://prove2.me/submissions/41d375c4-2201-4bff-a521-cc38c007cca2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    eventToMaster P J r e ≤ eventToMaster P J r f ↔ e ≤ f := Iff.rfl
end QEC.Coding.BDL26RandomPerturbation
