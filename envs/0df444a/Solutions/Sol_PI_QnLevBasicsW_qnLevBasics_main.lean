-- Prove2me | solution 1 for PI.QnLevBasicsW.qnLevBasics_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:35.97817+00:00
-- url     : https://prove2.me/submissions/f78a2f81-0b66-4a08-9927-ba2ccf51027d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_PI_QnLevBasicsW_level_group_homomorphism
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_hermitian
import Theorems.Thm_PI_QnLevBasicsW_level_group_nilpotent
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_weyl
import Theorems.Thm_PI_QnLevBasicsW_level_group_isotropic_vector
import Theorems.Thm_PI_QnLevBasicsW_level_group_ellipticity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution :
    LevHom ∧ LevUH ∧ LevN ∧ LevUW ∧ LevWb ∧ LevEll :=
  ⟨level_group_homomorphism, level_group_unitary_hermitian, level_group_nilpotent, level_group_unitary_weyl, level_group_isotropic_vector, level_group_ellipticity⟩
end PI.QnLevBasicsW
