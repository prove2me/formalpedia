-- Prove2me | solution 1 for PI.StabPairsW.det_ne_of_mem_GV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:40.693707+00:00
-- url     : https://prove2.me/submissions/5ab350c5-e47a-462c-b83b-ca6c01712833

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_hpk_det_ne
import Theorems.Thm_PI_StabPairsW_mem_GV_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution {g : B.Mat k r} (hg : g ∈ B.GV k r) : g.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (mem_GV_iff.1 hg)
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  exact hpk_det_ne h1.symm
end PI.StabPairsW
