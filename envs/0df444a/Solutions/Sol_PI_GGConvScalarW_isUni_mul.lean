-- Prove2me | solution 1 for PI.GGConvScalarW.isUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:28.712901+00:00
-- url     : https://prove2.me/submissions/7a7beb9b-183c-4fea-ad26-db82d5754336

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Theorems.Thm_PI_GGConvScalarW_IsUTm_mul

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
theorem _root_.solution {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by
  show IsUTm ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F))
  exact IsUTm.mul hx hy
end PI.GGConvScalarW
