-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.locSplit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:19.415718+00:00
-- url     : https://prove2.me/submissions/496cf548-a208-411d-8a79-9423acfcc639

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_chiV_props
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_modQ_of_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocSplitChi) : LocSplit := by
  unfold LocSplit
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _
end PI.UnitaryGroupMassFormula.AdIndexEq
