-- Prove2me | solution 1 for P2M.Dup.ModularCurve.transcendental_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/33715924-2df5-5663-b367-b2a947ad0b08

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_transcendental_jqNModC

set_option autoImplicit false

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand_coeff_mul qExpand_coeff_of_not_dvd algebraMap_laurentSeries_eq_single coeff_jqModC_pow_self coeff_jqModC_pow_of_lt"
p2m_open "ModularCurve"

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem coeff_jqNModC_pow_self (i : ℕ) : (jqNModC K N ^ i).coeff (-((N : ℤ) * i)) = 1 := by
  rw [jqNModC, ← map_pow, show -((N : ℤ) * i) = (N : ℤ) * (-(i : ℤ)) by ring, qExpand_coeff_mul,
    coeff_jqModC_pow_self]

theorem coeff_jqNModC_pow_of_lt (i : ℕ) {m : ℤ} (hm : m < -((N : ℤ) * i)) :
    (jqNModC K N ^ i).coeff m = 0 := by
  rw [jqNModC, ← map_pow]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    apply coeff_jqModC_pow_of_lt
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have h1 : (N : ℤ) * k < N * (-(i : ℤ)) := by linarith
    exact lt_of_mul_lt_mul_left h1 hN.le
  · exact qExpand_coeff_of_not_dvd N _ hdvd

theorem coeff_aeval_jqNModC_natDegree (P : K[X]) :
    (aeval (jqNModC K N) P).coeff (-((N : ℤ) * P.natDegree)) = P.leadingCoeff := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single P.natDegree]
  · rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jqNModC_pow_self, mul_one, leadingCoeff]
  · intro i hi hne
    have hid : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    have h1 : (i : ℤ) < P.natDegree := by exact_mod_cast hid
    rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jqNModC_pow_of_lt K N i (by nlinarith), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem coeff_aeval_jqNModC_of_lt (P : K[X]) {m : ℤ} (hm : m < -((N : ℤ) * P.natDegree)) :
    (aeval (jqNModC K N) P).coeff m = 0 := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (i : ℤ) ≤ P.natDegree := by exact_mod_cast hid
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
      coeff_jqNModC_pow_of_lt K N i (by nlinarith), mul_zero]

theorem order_aeval_jqNModC (P : K[X]) (hP : P ≠ 0) :
    (aeval (jqNModC K N) P).order = -((N : ℤ) * P.natDegree) := by
  have hlead : (aeval (jqNModC K N) P).coeff (-((N : ℤ) * P.natDegree)) ≠ 0 := by
    rw [coeff_aeval_jqNModC_natDegree]
    exact leadingCoeff_ne_zero.mpr hP
  have hne : aeval (jqNModC K N) P ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hlead
  apply le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hlead)
  by_contra h
  exact hne (HahnSeries.coeff_order_eq_zero.mp (coeff_aeval_jqNModC_of_lt K N P (not_le.mp h)))

theorem aeval_jqNModC_ne_zero (P : K[X]) (hP : P ≠ 0) : aeval (jqNModC K N) P ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero
    (by rw [coeff_aeval_jqNModC_natDegree]; exact leadingCoeff_ne_zero.mpr hP)

private theorem solution_impl : Transcendental K (jqNModC K N) :=
  fun ⟨P, hP0, hPx⟩ => aeval_jqNModC_ne_zero K N P hP0 hPx

theorem transcendental_jqModC : Transcendental K (jqModC K) := by
  simpa using solution_impl K 1

theorem order_aeval_jqNModC_div (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (aeval (jqNModC K N) P / aeval (jqNModC K N) Q).order = (N : ℤ) * Q.natDegree - (N : ℤ) * P.natDegree := by
  have hQ' := aeval_jqNModC_ne_zero K N Q hQ
  have hP' := aeval_jqNModC_ne_zero K N P hP
  have hdiv : aeval (jqNModC K N) P / aeval (jqNModC K N) Q ≠ 0 := div_ne_zero hP' hQ'
  have hmul : (aeval (jqNModC K N) P / aeval (jqNModC K N) Q * aeval (jqNModC K N) Q).order =
      (aeval (jqNModC K N) P / aeval (jqNModC K N) Q).order + (aeval (jqNModC K N) Q).order :=
    HahnSeries.order_mul hdiv hQ'
  rw [div_mul_cancel₀ _ hQ', order_aeval_jqNModC K N P hP, order_aeval_jqNModC K N Q hQ] at hmul
  linarith

end ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Transcendental K (ModularCurve.jqNModC K N) :=
  ModularCurve.solution_impl K N

end S_ModularCurve_transcendental_jqNModC
end P2MW
export P2MW.S_ModularCurve_transcendental_jqNModC (solution)
