-- Prove2me | solution 1 for PowerSeries.exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/99de94a0-46f1-599e-bbac-400a57f4ba71

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq

set_option autoImplicit false

universe u

open IsLocalRing

namespace IdealEqAux

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]

theorem X_sub_C_mul_eq_zero {z : T} (hz : z ∈ maximalIdeal T) {g : PowerSeries T}
    (h : (PowerSeries.X - PowerSeries.C z) * g = 0) : g = 0 := by

  have hrec : ∀ n, PowerSeries.coeff n g = z * PowerSeries.coeff (n + 1) g := by
    intro n
    have := congrArg (PowerSeries.coeff (n + 1)) h
    rw [sub_mul, map_sub, PowerSeries.coeff_succ_X_mul, ← PowerSeries.smul_eq_C_mul, PowerSeries.coeff_smul,
      map_zero, sub_eq_zero] at this
    rw [this, smul_eq_mul]
  have hpow : ∀ k n, PowerSeries.coeff n g = z ^ k * PowerSeries.coeff (n + k) g := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [ih n, hrec (n + k), pow_succ, mul_assoc, show n + k + 1 = n + (k + 1) by omega]
  ext n
  rw [map_zero]
  have hmem : PowerSeries.coeff n g ∈ ⨅ k : ℕ, maximalIdeal T ^ k := by
    rw [Ideal.mem_iInf]
    intro k
    rw [hpow k n]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hz k)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal T).ne_top, Ideal.mem_bot] at hmem

theorem prod_mul_eq_zero {ι : Type*} (S : Finset ι) (z : ι → T) (hz : ∀ i ∈ S, z i ∈ maximalIdeal T)
    {g : PowerSeries T} (h : (∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) * g = 0) : g = 0 := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_assoc] at h
    have h1 := X_sub_C_mul_eq_zero (hz a (Finset.mem_insert_self a s)) h
    exact ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) h1

end IdealEqAux

open IdealEqAux in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {ι : Type*} (S : Finset ι) (z : ι → T)
    (hz : ∀ i ∈ S, z i ∈ IsLocalRing.maximalIdeal T) (x : PowerSeries T)
    (h : Ideal.span {x} = Ideal.span {∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))}) :
    ∃ u : PowerSeries T, IsUnit u ∧ u * x = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i)) := by
  set p := ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i)) with hp
  have hx : x ∈ Ideal.span {p} := h ▸ Ideal.mem_span_singleton_self x
  have hpx : p ∈ Ideal.span {x} := h.symm ▸ Ideal.mem_span_singleton_self p
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hpx

  have hzero : p * (1 - b * a) = 0 := by
    have : p = b * a * p := by rw [mul_assoc, ha, hb]
    linear_combination this
  have hba : b * a = 1 := by
    have := prod_mul_eq_zero S z hz (by rw [hp] at hzero; exact hzero)
    exact (sub_eq_zero.mp this).symm
  exact ⟨b, IsUnit.of_mul_eq_one a hba, hb⟩

end S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq
end P2MW
export P2MW.S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq (solution)
