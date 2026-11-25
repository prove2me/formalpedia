-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.bd_int_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:58.793152+00:00
-- url     : https://prove2.me/submissions/7fb375ea-37f3-4675-90ec-a849efeaa9f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_BoundedRationalUnitary

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
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : K) * e) := by
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  exact ⟨y, hy0, by rwa [zsmul_eq_mul] at hyint⟩
end PI.UnitaryApproxFinWork
