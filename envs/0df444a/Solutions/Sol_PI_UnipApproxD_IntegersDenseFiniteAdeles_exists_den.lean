-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:23.928322+00:00
-- url     : https://prove2.me/submissions/296affb8-7d2e-4660-9f14-9e1e93236b5e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_int_R
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_den_local

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
theorem _root_.solution (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
    first
    | exact Filter.eventually_cofinite.mp b.2
    | exact Filter.eventually_cofinite.mp b.prop
  choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)
  refine ⟨∏ v ∈ hfin.toFinset, s v, Finset.prod_ne_zero_iff.mpr fun v _ => hs0 v, ?_⟩
  intro w
  have hc : (algebraMap R (FiniteAdeleRing R K) (∏ v ∈ hfin.toFinset, s v) * b) w
      = algebraMap K (w.adicCompletion K) (algebraMap R K (∏ v ∈ hfin.toFinset, s v)) * b w := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply]; rfl)
    | simp [IsScalarTower.algebraMap_apply R K (w.adicCompletion K)]
  rw [hc]
  by_cases hw : w ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, map_mul, map_mul, mul_assoc, mul_left_comm]
    exact mul_mem (int_R w _) (hs w)
  · have hbw : b w ∈ w.adicCompletionIntegers K := by
      simpa using hw
    exact mul_mem (int_R w _) hbw
end PI.UnipApproxD.IntegersDenseFiniteAdeles
