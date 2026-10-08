-- Prove2me | solution 1 for SphericalFerromagnet.shoot_five_undershoots
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-05T05:33:43.653558+00:00
-- url     : https://prove2.me/submissions/bb6f968a-35ab-4ec9-ae05-5e29015ee5be

import Definitions.Def_spherical_ferromagnet_shooting_defs
import Definitions.Def_sf241_shoot_bounds

open scoped ContDiff
open Real Set
open SphericalFerromagnet

theorem solution : ∀ h, ShootSol 5 h → h (π / 2) < π :=
  P241N.five_undershoots
