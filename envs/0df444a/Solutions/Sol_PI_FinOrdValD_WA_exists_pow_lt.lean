-- Prove2me | solution 1 for PI.FinOrdValD.WA.exists_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:37.751689+00:00
-- url     : https://prove2.me/submissions/2d6363dc-79d1-4ae3-9d56-c6c7bbe334b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution {δ : ℤᵐ⁰} (hδ : δ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < δ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, exp k = δ := ⟨log δ, exp_log hδ⟩
  refine ⟨k.natAbs + 1, ?_⟩
  rw [exp_lt_exp]
  omega
end PI.FinOrdValD.WA
