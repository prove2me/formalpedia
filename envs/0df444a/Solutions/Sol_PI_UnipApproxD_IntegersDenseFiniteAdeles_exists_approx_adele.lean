-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:33.907545+00:00
-- url     : https://prove2.me/submissions/31bbdbb8-44f9-4e94-beb7-47e6f296fa06

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_val_R
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_den
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_approx

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
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hc⟩ := exists_den (R := R) (K := K) b
  obtain ⟨a, ha⟩ := exists_approx (R := R) (K := K) _ hc r hr
  refine ⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩
  have hinj : Function.Injective (algebraMap R K) := by
    first
    | exact IsFractionRing.injective R K
    | exact IsFractionRing.injective
    | exact NoZeroSMulDivisors.algebraMap_injective R K
  have hrK : algebraMap R K r ≠ 0 := fun h => hr (hinj (by rw [h, map_zero]))
  have hx : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 := (map_ne_zero _).mpr hrK
  have e1 : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v
      = b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    first
    | rfl
    | simp
  have e2 : (algebraMap R (FiniteAdeleRing R K) r * b) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply]; rfl)
    | simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
  have h1 := ha v
  rw [e2] at h1
  have e3 : b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)
      = (algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ *
        (algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v
          - algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    rw [map_div₀]
    field_simp
  rw [e1, e3, mem_adicCompletionIntegers, map_mul, map_inv₀, val_R]
  have hne : v.intValuation r ≠ 0 := by
    rw [← val_R (K := K) v r]
    exact (Valuation.ne_zero_iff _).mpr hx
  calc (v.intValuation r)⁻¹ * Valued.v _ ≤ (v.intValuation r)⁻¹ * v.intValuation r :=
        by gcongr
    _ = 1 := inv_mul_cancel₀ hne
end PI.UnipApproxD.IntegersDenseFiniteAdeles
