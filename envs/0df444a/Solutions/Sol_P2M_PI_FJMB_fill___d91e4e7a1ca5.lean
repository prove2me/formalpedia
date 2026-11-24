-- Prove2me | solution 1 for P2M_PI_FJMB_fill___d91e4e7a1ca5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:28.318256+00:00
-- url     : https://prove2.me/submissions/13ddafbd-15d0-41a0-a81f-4e0e5670375a

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
theorem _root_.solution {K : Type*} {m n : ℕ} {ι : Fin m × Fin n → σ} (hι : Function.Injective ι) (M : Fin m → Fin n → K)
    (p : σ → K) (x : Fin m × Fin n) : fill ι M p (ι x) = M x.1 x.2 :=
  hι.extend_apply _ _ _
end PI.FJMB
