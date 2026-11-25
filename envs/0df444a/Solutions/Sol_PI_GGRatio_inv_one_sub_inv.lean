-- Prove2me | solution 1 for PI.GGRatio.inv_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:02.605478+00:00
-- url     : https://prove2.me/submissions/e62d7dba-0b98-4c8a-b495-c833ae811bfb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset
namespace PI.GGRatio
theorem _root_.solution (Q : ℝ) (hQ : 1 < Q) : (1 - Q⁻¹)⁻¹ = Q / (Q - 1) := by
  have h1 : Q ≠ 0 := by linarith
  have h2 : Q - 1 ≠ 0 := by linarith
  field_simp
end PI.GGRatio
