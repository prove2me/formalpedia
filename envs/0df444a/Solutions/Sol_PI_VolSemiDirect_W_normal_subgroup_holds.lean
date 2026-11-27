-- Prove2me | solution 1 for PI.VolSemiDirect.W.normal_subgroup_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:52.948052+00:00
-- url     : https://prove2.me/submissions/1ddf67b5-deee-41ab-802f-8ae1d8af8f2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
import Theorems.Thm_PI_VolSemiDirect_W_norm_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
namespace PI.VolSemiDirect.W
theorem _root_.solution : NormStep := by
  intro F E _ _ _ _ _ σ _ M J _ r P T _ _ h hh n hn
  exact norm_gen (AF F) σ J P h hh n hn
end PI.VolSemiDirect.W
