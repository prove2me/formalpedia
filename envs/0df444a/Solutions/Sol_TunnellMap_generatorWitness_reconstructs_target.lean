-- Prove2me | solution 1 for TunnellMap.generatorWitness_reconstructs_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:49.329424+00:00
-- url     : https://prove2.me/submissions/54729010-6e36-440c-ac8b-c2779cfd540a

import Definitions.Def_TunnellMap_GeneratorRecovery
import Definitions.Def_TunnellMap_GeneratorSoundness

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {s : BResidual n}
    {t : AResidual n} {R : PreferredMidpointRecord s t}
    (W : GeneratorWitness s t R) :
    residualTargetLift R.target =
      reconstructedTarget (residualSourceLift s) W.q R.direction := by
  rw [W.q_eq]
  exact R.target_formula
end TunnellMap
