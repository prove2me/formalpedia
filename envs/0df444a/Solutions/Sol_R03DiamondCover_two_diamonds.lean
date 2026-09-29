-- Prove2me | solution 1 for R03DiamondCover.two_diamonds
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T19:28:23.01595+00:00
-- url     : https://prove2.me/submissions/f15b0177-823c-4b07-8ead-08e11311c882

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

end R03DiamondCover

open R03DiamondCover
theorem solution : ∀ a b c d : Fin 3,
    Compose Diamond Diamond a b c d ↔ Full 2 a b c d := by
  unfold Compose Diamond Full forbidden
  decide +kernel
