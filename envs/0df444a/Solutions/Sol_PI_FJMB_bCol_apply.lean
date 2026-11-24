-- Prove2me | solution 1 for PI.FJMB.bCol_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:41.113053+00:00
-- url     : https://prove2.me/submissions/d60552f7-e9f5-4dad-a36e-15d279ad4152

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [PI.FJM.bCol, LinearMap.sum_apply]; simp
end PI.FJMB
