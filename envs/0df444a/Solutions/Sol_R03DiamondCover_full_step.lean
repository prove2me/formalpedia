-- Prove2me | solution 1 for R03DiamondCover.full_step
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:24.345403+00:00
-- url     : https://prove2.me/submissions/018cc48c-c7c2-4ccb-af74-feacb2d5dd56

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_09e80204d5_R03DiamondCover_v1

/- Candidate-only exact finite relations and arbitrary finite chain induction.
   The relation's interpretation as a physical diamond cover, switching-class
   classification and graph connectivity are separate graph proof candidates. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000
namespace R03DiamondCover

theorem two_diamonds : ∀ a b c d : Fin 3,
    Compose Diamond Diamond a b c d ↔ Full 2 a b c d := by
  unfold Compose Diamond Full forbidden
  decide +kernel


end R03DiamondCover

open R03DiamondCover
theorem solution : ∀ r a b c d : Fin 3,
    Compose (Full r) Diamond a b c d ↔ Full (r+1) a b c d := by
  unfold Compose Diamond Full forbidden
  decide +kernel
