-- Prove2me | solution 1 for PowerSeries.existsUnique_algHom_apply_X_eq_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c5a7ef7c-ec59-587b-b389-373e7ce26935

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent

set_option autoImplicit false

namespace EvalNilpAux
open PowerSeries

theorem coe_eq_aeval_X {A : Type} [CommRing A] (p : Polynomial A) :
    (p : PowerSeries A) = Polynomial.aeval (PowerSeries.X : PowerSeries A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.coe_monomial]
    ext m
    rw [PowerSeries.coeff_monomial, show (algebraMap A (PowerSeries A)) a = PowerSeries.C a from rfl,
      PowerSeries.coeff_C_mul_X_pow]

theorem apply_coe {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T]
    (φ : PowerSeries A →ₐ[A] T) (p : Polynomial A) : φ (p : PowerSeries A) = Polynomial.aeval (φ PowerSeries.X) p := by
  rw [coe_eq_aeval_X, ← Polynomial.aeval_algHom_apply]

theorem aeval_eq_sum_of_pow_eq_zero {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T]
    (t : T) (N : ℕ) (hN : t ^ N = 0) (p : Polynomial A) :
    Polynomial.aeval t p = ∑ i ∈ Finset.range N, algebraMap A T (p.coeff i) * t ^ i := by
  classical
  have hp : Polynomial.aeval t p = ∑ i ∈ Finset.range (max N (p.natDegree + 1)), p.coeff i • t ^ i :=
    Polynomial.aeval_eq_sum_range' (p := p) (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)) t
  rw [hp]
  have hsub : ∑ i ∈ Finset.range N, algebraMap A T (p.coeff i) * t ^ i =
      ∑ i ∈ Finset.range (max N (p.natDegree + 1)), algebraMap A T (p.coeff i) * t ^ i := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro i _ hnot
    have hge : N ≤ i := by simpa [Finset.mem_range] using hnot
    rw [show t ^ i = 0 from by rw [← Nat.add_sub_cancel' hge, pow_add, hN, zero_mul], mul_zero]
  rw [hsub]
  exact Finset.sum_congr rfl (fun i _ => Algebra.smul_def _ _)

theorem formula {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T]
    (φ : PowerSeries A →ₐ[A] T) (t : T) (hφ : φ PowerSeries.X = t) (N : ℕ) (hN : t ^ N = 0) (f : PowerSeries A) :
    φ f = ∑ i ∈ Finset.range N, algebraMap A T (PowerSeries.coeff i f) * t ^ i := by
  classical
  conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc N f]
  rw [map_add, map_mul, map_pow, hφ, hN, zero_mul, zero_add, apply_coe, hφ, aeval_eq_sum_of_pow_eq_zero t N hN]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hi)]

end EvalNilpAux

theorem solution
    {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) :
    (∃! φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t) ∧
    (∀ φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t → ∀ N : ℕ, t ^ N = 0 →
      ∀ f : PowerSeries A, φ f = ∑ i ∈ Finset.range N, algebraMap A T (PowerSeries.coeff i f) * t ^ i) := by
  classical
  obtain ⟨N₀, hN₀⟩ := ht
  set N : ℕ := N₀ + 2 with hNdef
  have hN : t ^ N = 0 := by rw [hNdef, pow_add, hN₀, zero_mul]
  let φ₀ : PowerSeries A → T := fun f => Polynomial.aeval t (PowerSeries.trunc N f)
  have hφ₀ : ∀ f, φ₀ f = Polynomial.aeval t (PowerSeries.trunc N f) := fun _ => rfl
  have htr : ∀ p : Polynomial A, Polynomial.aeval t (PowerSeries.trunc N (p : PowerSeries A)) = Polynomial.aeval t p := by
    intro p
    rw [EvalNilpAux.aeval_eq_sum_of_pow_eq_zero t N hN, EvalNilpAux.aeval_eq_sum_of_pow_eq_zero t N hN]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hi), Polynomial.coeff_coe]
  have hmul : ∀ f g, φ₀ (f * g) = φ₀ f * φ₀ g := by
    intro f g
    rw [hφ₀, hφ₀, hφ₀, ← map_mul, ← htr (PowerSeries.trunc N f * PowerSeries.trunc N g), Polynomial.coe_mul,
      PowerSeries.trunc_trunc_mul_trunc]
  let φ : PowerSeries A →ₐ[A] T :=
    { toFun := φ₀
      map_one' := by
        show Polynomial.aeval t (PowerSeries.trunc (N₀ + 1 + 1) 1) = 1
        rw [PowerSeries.trunc_one, map_one]
      map_mul' := hmul
      map_zero' := by show Polynomial.aeval t (PowerSeries.trunc N 0) = 0; rw [map_zero, map_zero]
      map_add' := fun f g => by
        show Polynomial.aeval t (PowerSeries.trunc N (f + g)) = _
        rw [map_add, map_add]
      commutes' := fun a => by
        show Polynomial.aeval t (PowerSeries.trunc (N₀ + 1 + 1) (algebraMap A (PowerSeries A) a)) = algebraMap A T a
        rw [show algebraMap A (PowerSeries A) a = PowerSeries.C a from rfl, PowerSeries.trunc_C, Polynomial.aeval_C] }
  have hφX : φ PowerSeries.X = t := by
    show Polynomial.aeval t (PowerSeries.trunc (N₀ + 2) PowerSeries.X) = t
    rw [PowerSeries.trunc_X, Polynomial.aeval_X]
  refine ⟨⟨φ, hφX, fun φ' hφ' => ?_⟩, fun φ' hφ' N' hN' f => EvalNilpAux.formula φ' t hφ' N' hN' f⟩
  ext f
  rw [EvalNilpAux.formula φ' t hφ' N hN f, EvalNilpAux.formula φ t hφX N hN f]

#print axioms solution

end S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent
end P2MW
export P2MW.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent (solution)
