-- Prove2me | solution 1 for PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a9e12a0f-2158-5b10-85df-8c850ba69671

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq

set_option autoImplicit false

open Coalgebra Bialgebra WithConv
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

namespace ConvLeibniz

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]
  {Λ : Type*} [CommSemiring Λ] [Algebra R Λ]

theorem sum_counit_right_smul_left {a : A} {ι : Type*} (𝓡 : Coalgebra.Repr R a ι) :
    ∑ i ∈ 𝓡.index, counit (R := R) (𝓡.right i) • 𝓡.left i = a := by
  have h := congrArg (TensorProduct.rid R A) (sum_tmul_counit_eq (R := R) 𝓡)
  rw [map_sum] at h
  simpa [TensorProduct.rid_tmul] using h

theorem sum_sum_sum_comm {ι κ μ : Type*} (s : Finset ι) (t : Finset κ) (u : Finset μ)
    (F : ι → κ → μ → Λ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ l ∈ u, F i j l = ∑ l ∈ u, ∑ i ∈ s, ∑ j ∈ t, F i j l := by
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem convPow_apply_mul' (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = counit (R := R) a • d b + counit (R := R) b • d a)
    (k : ℕ) (a b : A) :
    (toConv d ^ k) (a * b) =
      ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : Λ) * ((toConv d ^ j) a * (toConv d ^ (k - j)) b) := by

  set P : ℕ → A → Λ := fun j x => (toConv d ^ j) x with hP
  have hPsucc : ∀ (j : ℕ) (x : A) {ι_rx : Type _} (rx : Coalgebra.Repr R x ι_rx),
      ∑ i ∈ rx.index, P j (rx.left i) * d (rx.right i) = P (j + 1) x := by
    intro j x _ rx
    simp only [hP]
    rw [pow_succ, Coalgebra.Repr.convMul_apply rx]
  have hPcounit : ∀ (j : ℕ) (x : A) {ι_rx : Type _} (rx : Coalgebra.Repr R x ι_rx),
      ∑ i ∈ rx.index, counit (R := R) (rx.right i) • P j (rx.left i) = P j x := by
    intro j x _ rx
    have := sum_counit_right_smul_left (R := R) rx
    calc ∑ i ∈ rx.index, counit (R := R) (rx.right i) • P j (rx.left i)
        = P j (∑ i ∈ rx.index, counit (R := R) (rx.right i) • rx.left i) := by
          simp only [hP, map_sum, map_smul]
      _ = P j x := by rw [this]
  change P k (a * b) = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : Λ) * (P j a * P (k - j) b)
  induction k generalizing a b with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self,
      Nat.cast_one, one_mul, Nat.sub_zero, hP, pow_zero]
    rw [LinearMap.convOne_apply, LinearMap.convOne_apply, LinearMap.convOne_apply, counit_mul,
      map_mul]
  | succ k ih =>
    set ra := Coalgebra.Repr.arbitrary R a
    set rb := Coalgebra.Repr.arbitrary R b
    have hab : comul (R := R) (a * b) =
        ∑ i ∈ ra.index, ∑ j ∈ rb.index, (ra.left i * rb.left j) ⊗ₜ[R] (ra.right i * rb.right j) := by
      rw [comul_mul, ← ra.eq, ← rb.eq, Finset.sum_mul_sum]
      simp only [Algebra.TensorProduct.tmul_mul_tmul]

    have hL : P (k + 1) (a * b) =
        ∑ i ∈ ra.index, ∑ j ∈ rb.index,
          P k (ra.left i * rb.left j) * d (ra.right i * rb.right j) := by
      simp only [hP]
      rw [pow_succ, LinearMap.convMul_apply, hab]
      simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]

    have key : ∀ (i : A × A) (j' : A × A),
        P k (ra.left i * rb.left j') * d (ra.right i * rb.right j') =
        ∑ l ∈ Finset.range (k + 1), ((k.choose l : ℕ) : Λ) *
          ((counit (R := R) (ra.right i) • P l (ra.left i)) * (P (k - l) (rb.left j') * d (rb.right j')) +
           (P l (ra.left i) * d (ra.right i)) * (counit (R := R) (rb.right j') • P (k - l) (rb.left j'))) := by
      intro i j'
      rw [ih, hd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def]
      ring
    rw [hL]
    simp_rw [key]
    rw [sum_sum_sum_comm]
    have step : ∀ l ∈ Finset.range (k + 1),
        ∑ i ∈ ra.index, ∑ j' ∈ rb.index, ((k.choose l : ℕ) : Λ) *
          ((counit (R := R) (ra.right i) • P l (ra.left i)) * (P (k - l) (rb.left j') * d (rb.right j')) +
           (P l (ra.left i) * d (ra.right i)) * (counit (R := R) (rb.right j') • P (k - l) (rb.left j'))) =
        ((k.choose l : ℕ) : Λ) * (P l a * P (k - l + 1) b) +
          ((k.choose l : ℕ) : Λ) * (P (l + 1) a * P (k - l) b) := by
      intro l _
      simp_rw [← Finset.mul_sum]
      rw [← mul_add]
      congr 1
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, hPcounit l a ra, hPsucc (k - l) b rb,
        hPsucc l a ra, hPcounit (k - l) b rb]
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]

    rw [show k + 1 + 1 = k + 2 from rfl,
      Finset.sum_choose_succ_mul (fun l m => P l a * P m b) k]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    congr 3
    omega

end ConvLeibniz

universe u v w

theorem solution
    {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Bialgebra R A]
    {Λ : Type w} [CommSemiring Λ] [Algebra R Λ] (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = Coalgebra.counit (R := R) a • d b + Coalgebra.counit (R := R) b • d a)
    (k : ℕ) (a b : A) :
    (WithConv.toConv d ^ k).ofConv (a * b) =
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : Λ) *
        ((WithConv.toConv d ^ j).ofConv a * (WithConv.toConv d ^ (k - j)).ofConv b) :=
  ConvLeibniz.convPow_apply_mul' d hd k a b

end S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq
end P2MW
export P2MW.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq (solution)
