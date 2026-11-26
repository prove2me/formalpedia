-- Prove2me | solution 1 for P2M_Eden_radiusSq__nonneg_7729c3bfdb8d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:45.818081+00:00
-- url     : https://prove2.me/submissions/1645b377-33ab-4d8a-926c-7135bcdec694

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (p : PhaseSpace) : 0 ≤ radiusSq₂ p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)
end Eden
