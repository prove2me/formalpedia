-- Prove2me | solution 1 for P2M_PI_FJMF_bRow_apply__85c79f716ad7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:25.946463+00:00
-- url     : https://prove2.me/submissions/c33bdbeb-cd27-4502-8bce-3a194fb0d34f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)
namespace PI.FJMF
theorem _root_.solution (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  simp [PI.FJM.bRow, LinearMap.sum_apply, Module.End.mul_apply]
end PI.FJMF
