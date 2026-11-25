-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:02.834172+00:00
-- url     : https://prove2.me/submissions/7840c210-7603-4d31-ac5d-2c5c0c2aeb34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (T : GoodSet K G) (s : T.S) (f : Module.End K (T.W s)) :
    phi T s f = ∑ y : G, ((((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)) *
      LinearMap.trace K (T.W s) (f * T.tau s y⁻¹)) • MonoidAlgebra.of K G y := by
  simp [phi, LinearMap.sum_apply]
end PI.Dv.HermitianFormEquivalence
