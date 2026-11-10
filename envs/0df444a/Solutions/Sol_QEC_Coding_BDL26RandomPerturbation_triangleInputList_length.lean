-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleInputList_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:05:46.867025+00:00
-- url     : https://prove2.me/submissions/f51ddf0f-fd3e-4ecb-957f-7e112edbe0cf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Mathlib.Data.List.FinRange
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventKeyQuery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) :
    (triangleInputList P).length = Fintype.card (Triangle P) := List.length_ofFn
end QEC.Coding.BDL26RandomPerturbation
