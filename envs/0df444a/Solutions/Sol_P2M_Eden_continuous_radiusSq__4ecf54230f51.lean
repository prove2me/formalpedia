-- Prove2me | solution 1 for P2M_Eden_continuous_radiusSq__4ecf54230f51
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:04.287075+00:00
-- url     : https://prove2.me/submissions/a6f0f011-d9ad-4417-8370-71206c9a380c

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : Continuous radiusSq₁ := by
  unfold radiusSq₁
  fun_prop
end Eden
