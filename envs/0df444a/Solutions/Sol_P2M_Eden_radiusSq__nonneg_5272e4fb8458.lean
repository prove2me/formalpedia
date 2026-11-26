-- Prove2me | solution 1 for P2M_Eden_radiusSq__nonneg_5272e4fb8458
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:34.435669+00:00
-- url     : https://prove2.me/submissions/e7979a22-c9e3-47fc-8888-041ef443b20b

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (p : PhaseSpace) : 0 ≤ radiusSq₁ p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)
end Eden
