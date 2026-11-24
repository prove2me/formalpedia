-- Prove2me | solution 1 for PI.FJMS.idxP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.552075+00:00
-- url     : https://prove2.me/submissions/a23ec01e-76c6-46c6-a507-89971ed261b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_pos_iff_lt_nP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution {n : ℕ} (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i)
    (i : Fin n) (h : 0 < f i) : ∃ x : Fin (nP f), Fin.castLE (nP_le_nW f) x = i :=
  ⟨⟨i.val, (pos_iff_lt_nP f hseg i).1 h⟩, Fin.ext rfl⟩
end PI.FJMS
