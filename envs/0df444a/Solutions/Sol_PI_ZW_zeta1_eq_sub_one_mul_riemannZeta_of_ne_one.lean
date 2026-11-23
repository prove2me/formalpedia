-- Prove2me | solution 1 for PI.ZW.zeta1_eq_sub_one_mul_riemannZeta_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:37.573897+00:00
-- url     : https://prove2.me/submissions/6080cdb7-ab87-4d9f-b2b7-25d0eca61c81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightChi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Complex Filter Topology
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) : zeta1 s = (s - 1) * riemannZeta s := by
  show DirichletCharacter.LFunctionTrivChar₁ 1 s = _
  unfold DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs]
  simp [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
end PI.ZW
