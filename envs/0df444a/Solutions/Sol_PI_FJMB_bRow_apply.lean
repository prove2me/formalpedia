-- Prove2me | solution 1 for PI.FJMB.bRow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:56.396806+00:00
-- url     : https://prove2.me/submissions/78a53d2b-3c06-4c98-af16-ab0294806df2

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
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [PI.FJM.bRow, LinearMap.sum_apply]; simp
end PI.FJMB
