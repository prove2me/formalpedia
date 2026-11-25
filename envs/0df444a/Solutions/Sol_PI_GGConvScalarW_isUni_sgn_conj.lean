-- Prove2me | solution 1 for PI.GGConvScalarW.isUni_sgn_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:49.302611+00:00
-- url     : https://prove2.me/submissions/82302c58-fe32-4e84-afff-6f02a4ea6fb2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_isUTm_sgn_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGConvScalarW
theorem _root_.solution {u : GL (Fin k) F} (h : IsUni k u) : IsUni k (sgn k * u * sgn k) := by
  show IsUTm (sgnM (F := F) k * (u : Matrix (Fin k) (Fin k) F) * sgnM k)
  exact isUTm_sgn_conj h
end PI.GGConvScalarW
