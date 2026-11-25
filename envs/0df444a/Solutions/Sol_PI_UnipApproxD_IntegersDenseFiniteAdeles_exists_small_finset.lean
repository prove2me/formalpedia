-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:02.527807+00:00
-- url     : https://prove2.me/submissions/abedb8fa-8e6b-4534-b779-4b8a56b6d550

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_small

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
theorem _root_.solution (s : Finset (HeightOneSpectrum R)) (U : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K))
    (hU : ∀ v ∈ s, U v ∈ nhds (0 : v.adicCompletion K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ v ∈ s, ∀ y : v.adicCompletion K, Valued.v y ≤ v.intValuation r → y ∈ U v := by
  classical
  choose! r hr0 hr using fun v (hv : v ∈ s) => exists_small (R := R) (K := K) v (hU v hv)
  refine ⟨∏ w ∈ s, r w, Finset.prod_ne_zero_iff.mpr hr0, ?_⟩
  intro v hv y hy
  apply hr v hv y
  refine le_trans hy ?_
  rw [map_prod, ← Finset.mul_prod_erase s _ hv]
  apply mul_le_of_le_one_right'
  apply Finset.prod_le_one'
  intro w _
  first
  | exact v.intValuation_le_one (r w)
  | exact intValuation_le_one v (r w)
  | exact intValuation_le_one (r w)
end PI.UnipApproxD.IntegersDenseFiniteAdeles
