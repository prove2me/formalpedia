-- Prove2me | solution 1 for SphericalFerromagnet.shoot_three_overshoots
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-05T05:33:43.060189+00:00
-- url     : https://prove2.me/submissions/9c3e6c5e-a23c-4e99-b017-f68d53d63d80

import Definitions.Def_spherical_ferromagnet_shooting_defs
import Definitions.Def_sf241_shoot_bounds

open scoped ContDiff
open Real Set
open SphericalFerromagnet

theorem solution : ∀ h, ShootSol 3 h → π < h (π / 2) :=
  P241N.three_overshoots
