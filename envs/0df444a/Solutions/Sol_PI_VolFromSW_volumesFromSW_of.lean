-- Prove2me | solution 1 for PI.VolFromSW.volumesFromSW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:18.538821+00:00
-- url     : https://prove2.me/submissions/6af4c4ff-c7c0-4b82-a1e7-81bf7cbaa8bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolFromSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.VolFromSW
theorem _root_.solution (h1 : VolStabFromSW) (h2 : VolumeDegenerateFromSiegelWeil) : VolumesFromSW := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc
  exact ⟨h1 F E σ hE M J hJ ha hc, h2 F E σ hE M J hJ ha hc⟩
end PI.VolFromSW
