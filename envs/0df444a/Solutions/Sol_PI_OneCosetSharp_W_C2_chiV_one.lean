-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.chiV_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:16.980286+00:00
-- url     : https://prove2.me/submissions/b940a979-4471-458f-b299-7e488fbdcef3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution [DecidableEq k] (χ : kˣ →* ℂˣ) : chiV χ (1 : k) = 1 := by
  simp [PI.OneCosetSharp.chiV]
end PI.OneCosetSharp.W.C2
