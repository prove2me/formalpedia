-- Prove2me | solution 1 for PI.KLW.lattice_from_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:58.898216+00:00
-- url     : https://prove2.me/submissions/c80449b5-d5ad-40e8-99ab-8d691cf7de0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_lattice_from_norm_one_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution : LatticeFromNormOne := Ind.lattice_from_norm_one_induction
end PI.KLW
