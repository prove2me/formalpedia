-- Prove2me | solution 1 for PI.OkpW.natCard_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:01.293876+00:00
-- url     : https://prove2.me/submissions/1f2ce2e1-2421-44f4-acc6-b67c3ad5b72b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
namespace PI.OkpW
theorem _root_.solution (hK : Module.finrank ℚ K = 2) :
    Nat.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  have h := Ideal.absNorm_span_singleton (p : 𝓞 K)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h]
  have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
  simp
end PI.OkpW
