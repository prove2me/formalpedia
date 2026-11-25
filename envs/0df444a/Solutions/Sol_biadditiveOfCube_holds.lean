-- Prove2me | solution 1 for biadditiveOfCube_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:03:51.351434+00:00
-- url     : https://prove2.me/submissions/adb698ea-5d23-47f8-9a74-fd8889820c83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BiaddOfCube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_BiaddOfCube
import Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_assoc__f28fec791de9
import Theorems.Thm_P2M_PI_BiaddOfCubeWork_add_comm__d811c4cba816
import Theorems.Thm_PI_BiaddOfCubeWork_cc_Xv
import Theorems.Thm_PI_BiaddOfCubeWork_simeq_of_sub_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.BiaddOfCube.Target := by
  intro p _ l ex ph hex h hC
  have hxz : PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (PI.BiaddOfCube.Xv 2) = PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCube.Xv 0) :=
    PI.BiaddOfCubeWork.add_comm' l ex _ _
  have has := PI.BiaddOfCubeWork.add_assoc' hex h
    (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 1) (PI.BiaddOfCube.Xv 2)
    (PI.BiaddOfCubeWork.cc_Xv 0) (PI.BiaddOfCubeWork.cc_Xv 1) (PI.BiaddOfCubeWork.cc_Xv 2)
  constructor
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz]
    ring
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz, ← has]
    ring
