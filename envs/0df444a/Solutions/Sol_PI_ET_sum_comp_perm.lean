-- Prove2me | solution 1 for PI.ET.sum_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:40.440207+00:00
-- url     : https://prove2.me/submissions/a85e8e6c-b96b-406e-bd91-7d2d97f74097

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET
namespace PI.ET
theorem _root_.solution {M : Type*} [AddCommMonoid M] {k n : ℕ} (F : (Fin k → Fin n) → M)
    (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → Fin n, F (fun i => f (τ i)) = ∑ f, F f := (Equiv.arrowCongr τ.symm (Equiv.refl (Fin n))).sum_comp F
end PI.ET
