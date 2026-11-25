-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_den_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:29.886274+00:00
-- url     : https://prove2.me/submissions/6570e85d-97d2-4087-9c95-6167adb02556

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
theorem _root_.solution (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  obtain ⟨b, hb, h⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (R := R) (K := K) v y
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  first
  | (rw [← IsScalarTower.algebraMap_apply, mul_comm]; exact h)
  | (rw [mul_comm, ← IsScalarTower.algebraMap_apply]; exact h)
  | (simpa [mul_comm, ← IsScalarTower.algebraMap_apply] using h)
  | (convert h using 1; rw [mul_comm, IsScalarTower.algebraMap_apply R K]; rfl)
end PI.UnipApproxD.IntegersDenseFiniteAdeles
