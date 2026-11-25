-- Prove2me | solution 1 for PI.KLW.kerLocIso_of_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:04.741953+00:00
-- url     : https://prove2.me/submissions/4916005d-5e54-4139-9917-a6d7f5b5d0d9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_KerLocIsoOfNormOne
import Theorems.Thm_PI_KLW_lattice_from_norm_one
import Theorems.Thm_PI_KLW_lattice_reduction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution (h : NormOne) : PI.KerIso.LocIso := lattice_reduction (lattice_from_norm_one h)
end PI.KLW
