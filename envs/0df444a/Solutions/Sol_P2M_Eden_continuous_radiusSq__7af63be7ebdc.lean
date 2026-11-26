-- Prove2me | solution 1 for P2M_Eden_continuous_radiusSq__7af63be7ebdc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:10.796111+00:00
-- url     : https://prove2.me/submissions/6534eea7-be9e-4d40-b63a-20dd118a2fa3

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : Continuous radiusSq₂ := by
  unfold radiusSq₂
  fun_prop
end Eden
