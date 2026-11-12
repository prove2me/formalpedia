-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.centerSnapshotQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:51:17.557696+00:00
-- url     : https://prove2.me/submissions/26e60415-2d54-45c5-a1d5-b88d60127458

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (centerSnapshotQuery P J r lambda K e g).1 = eventCenter P J r lambda K e g := by
  rw [centerSnapshotQuery,pointSnapshotQuery_value]
  rfl
end QEC.Coding.BDL26RandomPerturbation
