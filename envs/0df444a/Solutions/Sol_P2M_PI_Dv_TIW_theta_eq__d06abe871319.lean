-- Prove2me | solution 1 for P2M_PI_Dv_TIW_theta_eq__d06abe871319
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:22.47455+00:00
-- url     : https://prove2.me/submissions/7d20452c-32b1-408e-900e-415188f39f7b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution (M : Module.End K (T.W s)) : theta T s M =
    ∑ y : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (M * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by
  simp only [theta, LinearMap.trace_mul_comm K (T.tau s _) M]
end PI.Dv.TIW
