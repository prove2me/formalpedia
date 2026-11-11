-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.continuous_oldAnchor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:57:25.217348+00:00
-- url     : https://prove2.me/submissions/f648384c-0eeb-48e0-92f0-414d00c43187

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
theorem _root_.solution (P : TannerSquarePresentation) (a : Triangle P) :
    Continuous (fun J : Vertex P → Space => oldAnchor P J a) := by
  change Continuous (fun J : Vertex P → Space => (1/2 : ℝ) • J (.x (P.faceX a.1)))
  exact (continuous_apply (Vertex.x (P.faceX a.1) : Vertex P)).const_smul (1/2 : ℝ)
end QEC.Coding.BDL26RandomPerturbation
