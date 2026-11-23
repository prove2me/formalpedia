-- Prove2me | solution 1 for PI.GGConvScalarW.sgn_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:40.492889+00:00
-- url     : https://prove2.me/submissions/6271a551-2c60-4826-a86c-5cc2f1670bff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    (sgnM (F := F) k * A * sgnM (F := F) k) i j = (-1 : F) ^ (i : ℕ) * A i j * (-1 : F) ^ (j : ℕ) := by
  unfold sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
end PI.GGConvScalarW
