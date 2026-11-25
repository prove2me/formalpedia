-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.conjMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:31.112557+00:00
-- url     : https://prove2.me/submissions/c0853570-7437-4121-adf9-37d586976123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_conj_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution : ConjMem := by
  intro b d x hx
  have hle : KF b d ≤ IntermediateField.comap ((starRingEnd ℂ).toRatAlgHom) (KF b d) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    show conj (UnitDetRootDefs.cmTheta b d) ∈ KF b d
    rw [conj_theta]
    exact sub_mem (IntermediateField.intCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
  exact hle hx
end PI.UnitaryGroupMassFormula.UnitDetRoot
