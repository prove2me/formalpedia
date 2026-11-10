-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.anchorCloseProgram_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:59:33.555188+00:00
-- url     : https://prove2.me/submissions/be850d1b-4d22-400b-8a0a-79b676796ec7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ColorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EligibilityQuery

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : anchorCloseProgram.cost ≤ 1000 := by decide
end QEC.Coding.BDL26RandomPerturbation
