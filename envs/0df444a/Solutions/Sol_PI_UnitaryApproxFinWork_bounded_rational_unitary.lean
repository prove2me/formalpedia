-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.bounded_rational_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:54:10.486696+00:00
-- url     : https://prove2.me/submissions/3b6b27db-1ade-4e0b-bd2a-fd6b2e8ccb0b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_BoundedRationalUnitary
import Theorems.Thm_PI_UnitaryApproxFinWork_bd_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : BddR := by
  intro F E _ _ _ _ _ v x
  obtain ⟨N, hN, h⟩ := bd_main v x
  refine ⟨(N : 𝓞 F), by exact_mod_cast hN, ?_⟩
  have e : dv E v (N : 𝓞 F) = (N : E ⊗[F] v.adicCompletion F) := by
    unfold dv
    simp [PI.UnitaryApproxDefs.inclE]
  rw [e]
  exact h
end PI.UnitaryApproxFinWork
