-- Prove2me | solution 1 for P2M_PI_FJMS_bRow_apply__fa8f98d64b0d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:58.417194+00:00
-- url     : https://prove2.me/submissions/df93e9f0-422b-4a4b-82f5-4cf5c4eed5de

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
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [bRow, LinearMap.sum_apply]; simp
end PI.FJMS
