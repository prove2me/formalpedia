-- Prove2me | solution 1 for PI.BiaddOfCubeWork.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:28.899773+00:00
-- url     : https://prove2.me/submissions/9bc53da4-19d7-4bff-a229-0d5a9048d25c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816
import Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
import Theorems.Thm_PI_BiaddOfCubeWork_simeq_of_sub_eq
import Theorems.Thm_PI_BiaddOfCubeWork_cc_Xv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BiaddOfCubeWork
open PI.BiaddOfCube
variable {p : ℕ} [Fact p.Prime]
variable {σ : Type*}
namespace PI.BiaddOfCubeWork
theorem _root_.solution : Target := by
  intro p _ l ex ph hex h hC
  constructor
  · refine simeq_of_sub_eq ?_ hC
    simp only [be]
    rw [add_comm' l ex (Xv 2) (Xv 0)]
    ring
  · refine simeq_of_sub_eq ?_ hC
    simp only [be]
    rw [add_comm' l ex (Xv 2) (Xv 0),
      add_assoc' hex h (Xv 0) (Xv 1) (Xv 2) (cc_Xv 0) (cc_Xv 1) (cc_Xv 2)]
    ring
end PI.BiaddOfCubeWork
