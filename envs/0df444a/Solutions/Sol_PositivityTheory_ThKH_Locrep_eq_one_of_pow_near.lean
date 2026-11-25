-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:07.414713+00:00
-- url     : https://prove2.me/submissions/f5178929-14b1-4002-822f-3d82f243daa5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LinearIndependentOfNotMem
import Theorems.Thm_UpperTheory_Reformulated_B_Yhd7_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R} (h : ∀ p : ℕ, ‖a ^ p - 1‖ < 1 / 2) :
    a = 1 :=
  _root_.UpperTheory.Reformulated.B.Yhd7.main h
end PositivityTheory.ThKH.Locrep
