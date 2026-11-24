-- Prove2me | solution 1 for PI.FJMS.pos_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:51.801711+00:00
-- url     : https://prove2.me/submissions/52b8d59f-a68b-4335-9714-2e77bec18468

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
    (x : Fin (nP f)) : 0 < f (Fin.castLE (nP_le_nW f) x) :=
  (pos_iff_lt_nP f hseg _).2 (by simp only [Fin.val_castLE]; exact x.isLt)
end PI.FJMS
