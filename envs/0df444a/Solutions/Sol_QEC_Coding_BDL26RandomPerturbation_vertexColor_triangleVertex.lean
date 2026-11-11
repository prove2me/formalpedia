-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.vertexColor_triangleVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:46:19.509731+00:00
-- url     : https://prove2.me/submissions/3a0efb0a-7928-4642-9bcc-f2ba44dc68d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (t : Triangle P) (i : Fin 3) :
    vertexColor P (triangleVertex P t i) = i := by
  fin_cases i <;> rfl
end QEC.Coding.BDL26RandomPerturbation
