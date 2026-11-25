-- Prove2me | solution 1 for PI.LatIdxDetW.neg_log_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:15.993921+00:00
-- url     : https://prove2.me/submissions/ef683885-9949-46c4-8d0d-55f0a73a479d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
namespace PI.LatIdxDetW
section Gen
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
end Gen
section Lat
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
private theorem neg_log_int_lemma_3 (w : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    - WithZero.log (w.valuation K (algebraMap R K r)) =
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r)) := by
  rw [w.valuation_of_algebraMap, w.intValuation_if_neg hr, WithZero.log_exp,
    ← FractionalIdeal.coeIdeal_span_singleton]
  have hJ : Ideal.span {r} ≠ 0 := by simpa using hr
  rw [FractionalIdeal.count_coe K w hJ]
  simp
variable [FiniteDimensional K V]
end Lat
end PI.LatIdxDetW
end
end

set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.LatIdxDetW
theorem _root_.solution (w : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    - WithZero.log (w.valuation K x) =
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton R⁰ x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0
  have hA : algebraMap R K a ≠ 0 := by
    intro h
    apply hx
    rw [h, zero_div]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hA (map_zero _)
  have e1 := neg_log_int_lemma_3 (K := K) w ha0
  have e2 := neg_log_int_lemma_3 (K := K) w hb0
  have hc := Formalism.DivisionValues.idxChange_cnt_mul (K := K) w hA (inv_ne_zero hB)
  have hc2 := Formalism.DivisionValues.idxChange_cnt_mul (K := K) w hB (inv_ne_zero hB)
  rw [mul_inv_cancel₀ hB, Formalism.DivisionValues.idxChange_cnt_one] at hc2
  have vA : w.valuation K (algebraMap R K a) ≠ 0 := (w.valuation K).ne_zero_iff.2 hA
  have vB : w.valuation K (algebraMap R K b) ≠ 0 := (w.valuation K).ne_zero_iff.2 hB
  rw [div_eq_mul_inv, hc, map_mul, map_inv₀, WithZero.log_mul vA (inv_ne_zero vB), WithZero.log_inv]
  linarith
end PI.LatIdxDetW
