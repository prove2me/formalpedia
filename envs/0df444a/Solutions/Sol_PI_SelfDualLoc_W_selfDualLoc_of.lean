-- Prove2me | solution 1 for PI.SelfDualLoc.W.selfDualLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:00.181748+00:00
-- url     : https://prove2.me/submissions/09f4b12a-373e-457c-b5c8-06442f945606

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfDirs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Theorems.Thm_PI_SelfDualLoc_W_fwdDir_of
import Theorems.Thm_PI_SelfDualLoc_W_bwdDir_of
import Theorems.Thm_PI_SelfDualLoc_W_selfDualLoc_of_dirs


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
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.SelfDualLoc.W
theorem _root_.solution (hS : SigInt) (hN : Nondeg) (hSp : SpanTop) (hL : LocBasis)
    (hD : DualBasis) (hU : UnitLoc) : PI.SelfDualLoc :=
  selfDualLoc_of_dirs (fwdDir_of hS) (bwdDir_of hN hSp hL hD hU)
end PI.SelfDualLoc.W
