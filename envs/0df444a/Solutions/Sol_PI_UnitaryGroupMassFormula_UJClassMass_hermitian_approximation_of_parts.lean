-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:49.611715+00:00
-- url     : https://prove2.me/submissions/cea75d44-3c54-468a-970f-5d595f068066

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_closeLoc_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_hermApprox_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hL : LocSw) (hT : TensLoc) (hC : LatClose) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := hermApprox_of hL (closeLoc_of hT hC) hW hB hG
end PI.UnitaryGroupMassFormula.UJClassMass
