-- Prove2me | solution 1 for P2M_PI_FJMS_bCol_apply__63c2c4b09970
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:58.220031+00:00
-- url     : https://prove2.me/submissions/0ba4062f-75dc-49b7-9d9b-288eb9daaa23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP

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
variable {σ κ : Type*} [Fintype κ]
namespace PI.FJMS
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [bCol, LinearMap.sum_apply]; simp
end PI.FJMS
