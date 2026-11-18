-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_D7_047
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:59:17.233896+00:00
-- url     : https://prove2.me/submissions/e1d379b8-5859-48b0-9c80-65330cd033c0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_047
open RealPinwheel.FiveSixths

theorem solution : ∀ j : Fin 26, witnessCheck (witnessD7_047 j) = true ∧ (witnessD7_047 j).length ≤ 352 := by
  decide +kernel
