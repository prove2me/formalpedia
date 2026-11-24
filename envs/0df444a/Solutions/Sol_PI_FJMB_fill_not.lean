-- Prove2me | solution 1 for PI.FJMB.fill_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:28.800261+00:00
-- url     : https://prove2.me/submissions/0cbbbed2-c422-412a-82c6-829071d78846

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
theorem _root_.solution {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K)
    (p : σ → K) (v : σ) (hv : ∀ x, ι x ≠ v) : fill ι M p v = p v :=
  Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hv x hx)
end PI.FJMB
