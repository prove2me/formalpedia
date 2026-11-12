-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.centerSnapshotQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:54:59.761228+00:00
-- url     : https://prove2.me/submissions/0304b286-dcfb-429c-a8f0-263f09eeea21

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_cost_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (centerSnapshotQuery P J r lambda K e g).2 ≤ 45 := pointSnapshotQuery_cost_le _ _ _
end QEC.Coding.BDL26RandomPerturbation
