-- Prove2me | solution 1 for PI.SelfDualLoc.W.selfDualLoc_of_dirs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:34.853833+00:00
-- url     : https://prove2.me/submissions/be590f26-0462-4ee2-9bd0-96b506050836

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfDirs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
namespace PI.SelfDualLoc.W
theorem _root_.solution (hF : FwdDir) (hB : BwdDir) : PI.SelfDualLoc := by
  intro F E _ _ _ _ _ n σ J v Lb T hfin hint hdual hT y
  exact ⟨fun hy z hz => hF F E n σ J v Lb hint y hy z hz,
    fun h => hB F E n σ J v Lb T hfin hint hdual hT y h⟩
end PI.SelfDualLoc.W
