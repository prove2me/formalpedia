-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/36ca143b-7979-5674-89ae-a62d104da430

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u

namespace Casimir29

variable {a b : ℚ}

theorem re_mul_comm (x y : ℍ[ℚ, a, b]) : (x * y).re = (y * x).re := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk]; ring

theorem trd_mul_comm (x y : ℍ[ℚ, a, b]) : trd (x * y) = trd (y * x) := by
  simp only [trd, re_mul_comm]

theorem trd_star' (x : ℍ[ℚ, a, b]) : trd (star x) = trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]

theorem trd_add' (x y : ℍ[ℚ, a, b]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y; simp [trd]; ring

theorem trd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : trd (c • x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]; ring

theorem trd_neg' (x : ℍ[ℚ, a, b]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]

theorem trd_sub' (x y : ℍ[ℚ, a, b]) : trd (x - y) = trd x - trd y := by
  rw [sub_eq_add_neg, trd_add', trd_neg']; ring

theorem trd_one' : trd (1 : ℍ[ℚ, a, b]) = 2 := by simp [trd]

theorem trd_coe' (r : ℚ) : trd ((r : ℚ) : ℍ[ℚ, a, b]) = 2 * r := by simp [trd]

theorem sq_eq_smul_of_re_eq_zero {x : ℍ[ℚ, a, b]} (h : x.re = 0) : x * x = (-nrd x) • (1 : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp at h; subst h
  ext <;> simp [nrd] <;> ring

theorem re_eq_zero_of_mul_self {μ : ℍ[ℚ, a, b]} {s : ℚ} (hs : s < 0) (hμ : μ * μ = s • (1 : ℍ[ℚ, a, b])) :
    μ.re = 0 := by
  obtain ⟨m₀, m₁, m₂, m₃⟩ := μ
  by_contra h
  have hI := congrArg QuaternionAlgebra.imI hμ
  have hJ := congrArg QuaternionAlgebra.imJ hμ
  have hK := congrArg QuaternionAlgebra.imK hμ
  have hR := congrArg QuaternionAlgebra.re hμ
  simp only [mk_mul_mk] at hI hJ hK hR
  simp at hI hJ hK hR h
  have h1 : m₁ = 0 := by
    have : m₀ * m₁ * 2 = 0 := by linarith
    simpa [h] using this
  have h2 : m₂ = 0 := by
    have : m₀ * m₂ * 2 = 0 := by linarith
    simpa [h] using this
  have h3 : m₃ = 0 := by
    have : m₀ * m₃ * 2 = 0 := by nlinarith
    simpa [h] using this
  subst h1 h2 h3
  have : m₀ * m₀ = s := by simpa using hR
  nlinarith

theorem star_eq_neg_of_re_eq_zero {μ : ℍ[ℚ, a, b]} (h : μ.re = 0) : star μ = -μ := by
  obtain ⟨m₀, m₁, m₂, m₃⟩ := μ
  simp at h; subst h
  ext <;> simp

theorem re_eq_zero_iff_trd {x : ℍ[ℚ, a, b]} : x.re = 0 ↔ trd x = 0 := by
  simp [trd]

theorem re_part_of_central {x : ℍ[ℚ, a, b]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hi : x * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * x) (hj : x * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * x) :
    x = ((x.re : ℚ) : ℍ[ℚ, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have h1 := congrArg QuaternionAlgebra.imJ hi
  have h2 := congrArg QuaternionAlgebra.imK hi
  have h3 := congrArg QuaternionAlgebra.imI hj
  have h4 := congrArg QuaternionAlgebra.imK hj
  simp only [mk_mul_mk] at h1 h2 h3 h4
  simp at h1 h2 h3 h4
  have e3 : x₃ = 0 := by
    rcases mul_eq_zero.mp (by linarith : a * x₃ * 2 = 0) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h ha
      · exact h
    · norm_num at h
  have e2 : x₂ = 0 := by
    have : x₂ * 2 = 0 := by linarith
    simpa using this
  have e1 : x₁ = 0 := by
    have : x₁ * 2 = 0 := by linarith
    simpa using this
  subst e1 e2 e3
  ext <;> simp

section Setup

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)

def sS (q q' : ℕ) : ℚ := ((q * q' : ℕ) : ℚ)

theorem sS_pos : 0 < sS q q' := by
  unfold sS; exact_mod_cast Nat.mul_pos (Fact.out : q.Prime).pos (Fact.out : q'.Prime).pos

include hμ in
theorem hmu' : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (-(sS q q')) • (1 : ℍ[ℚ, a, b]) := by
  rw [hμ, neg_smul]; rfl

include hμ in
theorem mu_re : (μ : ℍ[ℚ, a, b]).re = 0 :=
  re_eq_zero_of_mul_self (s := -(sS q q')) (by have := sS_pos (q := q) (q' := q'); linarith) (hmu' μ hμ)

include hμ in
theorem star_mu : Star.star (μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) :=
  star_eq_neg_of_re_eq_zero (mu_re μ hμ)

include hμ in
theorem trd_mu : trd (μ : ℍ[ℚ, a, b]) = 0 := by simp [trd, mu_re μ hμ]

include hμ in
theorem mu_cancel {x y : ℍ[ℚ, a, b]} (h : (μ : ℍ[ℚ, a, b]) * x = (μ : ℍ[ℚ, a, b]) * y) : x = y := by
  have h2 : (μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * x) = (μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * y) := by rw [h]
  rw [← mul_assoc, ← mul_assoc, hmu' μ hμ, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul] at h2
  exact smul_right_injective _ (by have := sS_pos (q := q) (q' := q'); intro h0; linarith) h2

include hμ in
theorem mu_mu_mul (y : ℍ[ℚ, a, b]) : (μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * y) = (-(sS q q')) • y := by
  rw [← mul_assoc, hmu' μ hμ, smul_mul_assoc, one_mul]

include hμ in
theorem mul_mu_mu (y : ℍ[ℚ, a, b]) : y * (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (-(sS q q')) • y := by
  rw [mul_assoc, hmu' μ hμ, mul_smul_comm, mul_one]

def sigma (v : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] := (-(sS q q')⁻¹) • ((μ : ℍ[ℚ, a, b]) * Star.star v * (μ : ℍ[ℚ, a, b]))

include hμ in
theorem mu_sigma (v : ℍ[ℚ, a, b]) : (μ : ℍ[ℚ, a, b]) * sigma (q := q) (q' := q') μ v = Star.star v * (μ : ℍ[ℚ, a, b]) := by
  unfold sigma
  rw [mul_smul_comm, ← mul_assoc, mu_mu_mul μ hμ, smul_mul_assoc, smul_smul]
  have : -(sS q q')⁻¹ * -sS q q' = 1 := by
    have := sS_pos (q := q) (q' := q'); field_simp
  rw [this, one_smul]

include hμ hstar in
theorem sigma_coe (x : ↥Λ) : sigma (q := q) (q' := q') μ (x : ℍ[ℚ, a, b]) = (star x : ℍ[ℚ, a, b]) :=
  mu_cancel μ hμ (by rw [mu_sigma μ hμ, hstar])

theorem sigma_add (u v : ℍ[ℚ, a, b]) :
    sigma (q := q) (q' := q') μ (u + v) = sigma (q := q) (q' := q') μ u + sigma (q := q) (q' := q') μ v := by
  unfold sigma; rw [star_add, mul_add, add_mul, smul_add]

theorem sigma_smul (c : ℚ) (v : ℍ[ℚ, a, b]) :
    sigma (q := q) (q' := q') μ (c • v) = c • sigma (q := q) (q' := q') μ v := by
  unfold sigma
  rw [show Star.star (c • v) = c • Star.star v by ext <;> simp, mul_smul_comm, smul_mul_assoc, smul_comm]

theorem sigma_sub (u v : ℍ[ℚ, a, b]) :
    sigma (q := q) (q' := q') μ (u - v) = sigma (q := q) (q' := q') μ u - sigma (q := q) (q' := q') μ v := by
  rw [sub_eq_add_neg, sigma_add, ← neg_one_smul ℚ v, sigma_smul, neg_one_smul, ← sub_eq_add_neg]

include hμ in
theorem sigma_mul (u v : ℍ[ℚ, a, b]) :
    sigma (q := q) (q' := q') μ (u * v) = sigma (q := q) (q' := q') μ v * sigma (q := q) (q' := q') μ u := by
  apply mu_cancel μ hμ
  rw [mu_sigma μ hμ, ← mul_assoc, mu_sigma μ hμ, mul_assoc, mu_sigma μ hμ, ← mul_assoc, StarMul.star_mul]

include hμ in
theorem sigma_sigma (v : ℍ[ℚ, a, b]) : sigma (q := q) (q' := q') μ (sigma (q := q) (q' := q') μ v) = v := by
  apply mu_cancel μ hμ
  rw [mu_sigma μ hμ]
  have h := congrArg Star.star (mu_sigma (q := q) (q' := q') μ hμ v)
  rw [StarMul.star_mul, StarMul.star_mul, star_star, star_mu μ hμ, mul_neg, neg_mul, neg_inj] at h
  exact h

include hμ in
theorem sigma_one : sigma (q := q) (q' := q') μ (1 : ℍ[ℚ, a, b]) = 1 :=
  mu_cancel μ hμ (by rw [mu_sigma μ hμ, star_one, one_mul, mul_one])

include hμ in
theorem sigma_mu : sigma (q := q) (q' := q') μ (μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) :=
  mu_cancel μ hμ (by rw [mu_sigma μ hμ, star_mu μ hμ, mul_neg, neg_mul])

include hμ in
theorem trd_sigma (v : ℍ[ℚ, a, b]) : trd (sigma (q := q) (q' := q') μ v) = trd v := by
  unfold sigma
  rw [trd_smul', trd_mul_comm, ← mul_assoc, hmu' μ hμ, smul_mul_assoc, one_mul, trd_smul', trd_star']
  have := sS_pos (q := q) (q' := q'); field_simp

def form (u v : ℍ[ℚ, a, b]) : ℚ := trd (u * sigma (q := q) (q' := q') μ v)

include hμ in
theorem form_symm (u v : ℍ[ℚ, a, b]) : form (q := q) (q' := q') μ u v = form (q := q) (q' := q') μ v u := by
  unfold form
  rw [← trd_sigma μ hμ (v * sigma μ u), sigma_mul μ hμ, sigma_sigma μ hμ]

include hμ in

theorem form_mul_left (u x v : ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ (u * x) v = form (q := q) (q' := q') μ u (v * sigma (q := q) (q' := q') μ x) := by
  unfold form
  rw [sigma_mul μ hμ, sigma_sigma μ hμ, mul_assoc]

theorem form_add_left (u u' v : ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ (u + u') v = form (q := q) (q' := q') μ u v + form (q := q) (q' := q') μ u' v := by
  unfold form; rw [add_mul, trd_add']

theorem form_smul_left (c : ℚ) (u v : ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ (c • u) v = c * form (q := q) (q' := q') μ u v := by
  unfold form; rw [smul_mul_assoc, trd_smul']

theorem form_add_right (u v v' : ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ u (v + v') = form (q := q) (q' := q') μ u v + form (q := q) (q' := q') μ u v' := by
  unfold form; rw [sigma_add, mul_add, trd_add']

theorem form_smul_right (c : ℚ) (u v : ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ u (c • v) = c * form (q := q) (q' := q') μ u v := by
  unfold form; rw [sigma_smul, mul_smul_comm, trd_smul']

end Setup

section Nu

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))

include hB in
theorem a_ne_zero : a ≠ 0 := by
  intro ha
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.imI h; simp at this
  have hu := hB.isUnit_of_ne_zero _ hi
  have hsq : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by
    ext <;> simp [ha]
  have := (hu.mul hu)
  rw [hsq] at this
  exact not_isUnit_zero this

include hB in
theorem b_ne_zero : b ≠ 0 := by
  intro hb
  have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
    intro h; have := congrArg QuaternionAlgebra.imJ h; simp at this
  have hu := hB.isUnit_of_ne_zero _ hj
  have hsq : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by
    ext <;> simp [hb]
  have := (hu.mul hu)
  rw [hsq] at this
  exact not_isUnit_zero this

include hB hΛ hμ in

theorem exists_not_commute : ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * y ≠ y * μ := by
  by_contra h
  push_neg at h

  let C : Submodule ℚ ℍ[ℚ, a, b] :=
    { carrier := {y | (μ : ℍ[ℚ, a, b]) * y = y * μ}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢; rw [mul_add, add_mul, hx, hy]
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; rw [mul_smul_comm, smul_mul_assoc, hx] }
  have hC : (⊤ : Submodule ℚ ℍ[ℚ, a, b]) ≤ C := by
    rw [← hΛ.spanTop, Submodule.span_le]
    intro y hy
    exact h ⟨y, hy⟩
  have hi : (μ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * μ := hC (Submodule.mem_top : (⟨0,1,0,0⟩ : ℍ[ℚ, a, b]) ∈ ⊤)
  have hj : (μ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * μ := hC (Submodule.mem_top : (⟨0,0,1,0⟩ : ℍ[ℚ, a, b]) ∈ ⊤)
  have hcen := re_part_of_central (a_ne_zero hB) (b_ne_zero hB) hi hj
  rw [mu_re μ hμ] at hcen
  have h0 : (μ : ℍ[ℚ, a, b]) = 0 := by rw [hcen]; simp
  have := hmu' μ hμ
  rw [h0, zero_mul] at this
  have := congrArg QuaternionAlgebra.re this
  simp at this
  have := sS_pos (q := q) (q' := q')
  linarith

noncomputable def nu (hB : IsIndefiniteRamifiedExactlyAt a b q q') (hΛ : IsOrder Λ) (μ : ↥Λ)
    (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) : ↥Λ :=
  ⟨(μ : ℍ[ℚ, a, b]) * (exists_not_commute hB hΛ μ hμ).choose - (exists_not_commute hB hΛ μ hμ).choose * μ,
    Λ.sub_mem (hΛ.mul_mem μ.2 (exists_not_commute hB hΛ μ hμ).choose.2)
      (hΛ.mul_mem (exists_not_commute hB hΛ μ hμ).choose.2 μ.2)⟩

theorem nu_ne_zero : (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) ≠ 0 := by
  have := (exists_not_commute hB hΛ μ hμ).choose_spec
  unfold nu
  simp only [Submodule.coe_mk]
  exact sub_ne_zero.mpr this

theorem mu_nu : (μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) = -((nu hB hΛ μ hμ : ℍ[ℚ, a, b]) * μ) := by
  unfold nu
  simp only [Submodule.coe_mk]
  rw [mul_sub, sub_mul, mu_mu_mul μ hμ, mul_mu_mu μ hμ, ← mul_assoc]
  abel

theorem nu_re : (nu hB hΛ μ hμ : ℍ[ℚ, a, b]).re = 0 := by
  have := re_mul_comm (μ : ℍ[ℚ, a, b]) ((exists_not_commute hB hΛ μ hμ).choose : ℍ[ℚ, a, b])
  show ((μ : ℍ[ℚ, a, b]) * ((exists_not_commute hB hΛ μ hμ).choose : ℍ[ℚ, a, b]) -
    ((exists_not_commute hB hΛ μ hμ).choose : ℍ[ℚ, a, b]) * μ).re = 0
  rw [show ∀ x y : ℍ[ℚ, a, b], (x - y).re = x.re - y.re from fun _ _ => rfl, this, sub_self]

noncomputable def dd : ℚ := -nrd (nu hB hΛ μ hμ : ℍ[ℚ, a, b])

theorem nu_nu : (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) = (dd hB hΛ μ hμ) • (1 : ℍ[ℚ, a, b]) :=
  sq_eq_smul_of_re_eq_zero (nu_re hB hΛ μ hμ)

theorem star_nu : Star.star (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) = -(nu hB hΛ μ hμ : ℍ[ℚ, a, b]) :=
  star_eq_neg_of_re_eq_zero (nu_re hB hΛ μ hμ)

theorem dd_ne_zero : dd hB hΛ μ hμ ≠ 0 := by
  intro h
  have hu := hB.isUnit_of_ne_zero _ (nu_ne_zero hB hΛ μ hμ)
  have := hu.mul hu
  rw [nu_nu, h, zero_smul] at this
  exact not_isUnit_zero this

theorem sigma_nu : sigma (q := q) (q' := q') μ (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) = (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) :=
  mu_cancel μ hμ (by rw [mu_sigma μ hμ, star_nu, mu_nu, neg_mul])

theorem sigma_mu_nu : sigma (q := q) (q' := q') μ ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) =
    (μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) := by
  rw [sigma_mul μ hμ, sigma_nu, sigma_mu μ hμ, mul_neg, mu_nu]

theorem mu_nu_sq : ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) * ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) =
    (sS q q' * dd hB hΛ μ hμ) • (1 : ℍ[ℚ, a, b]) := by
  set ν := (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) with hν
  have hνμ : ν * (μ : ℍ[ℚ, a, b]) = -((μ : ℍ[ℚ, a, b]) * ν) := by rw [hν, mu_nu]; simp
  have h1 : (μ : ℍ[ℚ, a, b]) * ν * ((μ : ℍ[ℚ, a, b]) * ν) = -((μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * (ν * ν))) := by
    calc (μ : ℍ[ℚ, a, b]) * ν * ((μ : ℍ[ℚ, a, b]) * ν) = (μ : ℍ[ℚ, a, b]) * ((ν * (μ : ℍ[ℚ, a, b])) * ν) := by
          simp only [mul_assoc]
      _ = -((μ : ℍ[ℚ, a, b]) * ((μ : ℍ[ℚ, a, b]) * (ν * ν))) := by rw [hνμ]; simp only [neg_mul, mul_neg, mul_assoc]
  rw [h1, hν, nu_nu, mu_mu_mul μ hμ, smul_smul, ← neg_smul]
  congr 1; ring

noncomputable def W : Fin 4 → ℍ[ℚ, a, b] :=
  ![1, (μ : ℍ[ℚ, a, b]), (nu hB hΛ μ hμ : ℍ[ℚ, a, b]), (μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])]

noncomputable def rr : Fin 4 → ℚ :=
  ![2, 2 * sS q q', 2 * dd hB hΛ μ hμ, 2 * (sS q q' * dd hB hΛ μ hμ)]

theorem W_mem (i : Fin 4) : W hB hΛ μ hμ i ∈ Λ := by
  fin_cases i
  · exact hΛ.one_mem
  · exact μ.2
  · exact (nu hB hΛ μ hμ).2
  · exact hΛ.mul_mem μ.2 (nu hB hΛ μ hμ).2

theorem trd_nu : trd (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) = 0 := by simp [trd, nu_re]

theorem trd_mu_nu : trd ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) = 0 := by
  have h := trd_mul_comm (μ : ℍ[ℚ, a, b]) (nu hB hΛ μ hμ : ℍ[ℚ, a, b])
  rw [mu_nu, trd_neg'] at h ⊢
  linarith

theorem trd_W_mul_W (i j : Fin 4) :
    trd (W hB hΛ μ hμ i * W hB hΛ μ hμ j) =
      if i = j then (![2, -(2 * sS q q'), 2 * dd hB hΛ μ hμ, 2 * (sS q q' * dd hB hΛ μ hμ)] : Fin 4 → ℚ) i else 0 := by
  set ν := (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) with hν
  set m := (μ : ℍ[ℚ, a, b]) with hm
  have t1 : trd (1 : ℍ[ℚ, a, b]) = 2 := trd_one'
  have tμ : trd m = 0 := trd_mu μ hμ
  have tν : trd ν = 0 := trd_nu hB hΛ μ hμ
  have tμν : trd (m * ν) = 0 := trd_mu_nu hB hΛ μ hμ
  have hμμ : m * m = (-(sS q q')) • (1 : ℍ[ℚ, a, b]) := hmu' μ hμ
  have hνν : ν * ν = (dd hB hΛ μ hμ) • (1 : ℍ[ℚ, a, b]) := nu_nu hB hΛ μ hμ
  have hνμ : ν * m = -(m * ν) := by rw [hν, hm, mu_nu]; simp
  have hμμx : ∀ x : ℍ[ℚ, a, b], m * (m * x) = (-(sS q q')) • x := mu_mu_mul μ hμ
  have p11 : trd (m * m) = -(2 * sS q q') := by rw [hμμ, trd_smul', t1]; ring
  have p13 : trd (m * (m * ν)) = 0 := by rw [hμμx, trd_smul', tν, mul_zero]
  have p21 : trd (ν * m) = 0 := by rw [hνμ, trd_neg', tμν, neg_zero]
  have p22 : trd (ν * ν) = 2 * dd hB hΛ μ hμ := by rw [hνν, trd_smul', t1]; ring
  have p23 : trd (ν * (m * ν)) = 0 := by
    rw [← mul_assoc, hνμ, neg_mul, trd_neg', mul_assoc, hνν, mul_smul_comm, mul_one, trd_smul', tμ]; ring
  have p31 : trd (m * ν * m) = 0 := by rw [mul_assoc, hνμ, mul_neg, trd_neg', hμμx, trd_smul', tν]; ring
  have p32 : trd (m * ν * ν) = 0 := by rw [mul_assoc, hνν, mul_smul_comm, mul_one, trd_smul', tμ]; ring
  have p33 : trd (m * ν * (m * ν)) = 2 * (sS q q' * dd hB hΛ μ hμ) := by
    rw [hm, hν, mu_nu_sq hB hΛ μ hμ, trd_smul', t1]; ring
  fin_cases i <;> fin_cases j <;>
    simp [W, ← hm, ← hν, t1, tμ, tν, tμν, p11, p13, p21, p22, p23, p31, p32, p33]

theorem sigma_W (j : Fin 4) :
    sigma (q := q) (q' := q') μ (W hB hΛ μ hμ j) = ((![1, -1, 1, 1] : Fin 4 → ℚ) j) • W hB hΛ μ hμ j := by
  have e1 := sigma_one (q := q) (q' := q') μ hμ
  have e2 := sigma_mu (q := q) (q' := q') μ hμ
  have e3 := sigma_nu hB hΛ μ hμ
  have e4 := sigma_mu_nu hB hΛ μ hμ
  fin_cases j <;> simp [W, e1, e2, e3, e4]

theorem form_W (i j : Fin 4) :
    form (q := q) (q' := q') μ (W hB hΛ μ hμ i) (W hB hΛ μ hμ j) = if i = j then rr hB hΛ μ hμ i else 0 := by
  unfold form
  rw [sigma_W, mul_smul_comm, trd_smul', trd_W_mul_W]
  fin_cases i <;> fin_cases j <;> simp [rr]

end Nu

section BasisPart

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))

noncomputable def formLin : ℍ[ℚ, a, b] →ₗ[ℚ] ℍ[ℚ, a, b] →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (form (q := q) (q' := q') μ) (form_add_left μ) (form_smul_left μ) (form_add_right μ) (form_smul_right μ)

@[scoped simp] theorem formLin_apply (u v : ℍ[ℚ, a, b]) : formLin (q := q) (q' := q') μ u v = form (q := q) (q' := q') μ u v := rfl

theorem form_sum_smul_left (c : Fin 4 → ℚ) (v : ℍ[ℚ, a, b]) (u : Fin 4 → ℍ[ℚ, a, b]) :
    form (q := q) (q' := q') μ (∑ j, c j • u j) v = ∑ j, c j * form (q := q) (q' := q') μ (u j) v := by
  rw [← formLin_apply, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, formLin_apply, smul_eq_mul]

theorem rr_ne_zero (i : Fin 4) : rr hB hΛ μ hμ i ≠ 0 := by
  have hs := sS_pos (q := q) (q' := q')
  have hd := dd_ne_zero hB hΛ μ hμ
  fin_cases i <;> simp [rr, hs.ne', hd]

theorem coeff_eq (c : Fin 4 → ℚ) (k : Fin 4) :
    form (q := q) (q' := q') μ (∑ j, c j • W hB hΛ μ hμ j) (W hB hΛ μ hμ k) = c k * rr hB hΛ μ hμ k := by
  rw [form_sum_smul_left]
  simp only [form_W hB hΛ μ hμ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem linearIndependent_W : LinearIndependent ℚ (W hB hΛ μ hμ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have := coeff_eq hB hΛ μ hμ c k
  rw [hc] at this
  unfold form at this
  rw [zero_mul, trd] at this
  simp at this
  rcases this with h | h
  · exact h
  · exact absurd h (rr_ne_zero hB hΛ μ hμ k)

noncomputable def bW : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b] :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_W hB hΛ μ hμ)
    (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])

theorem bW_apply (j : Fin 4) : bW hB hΛ μ hμ j = W hB hΛ μ hμ j := by
  simp [bW]

theorem expansion (z : ℍ[ℚ, a, b]) :
    z = ∑ j, (form (q := q) (q' := q') μ z (W hB hΛ μ hμ j) / rr hB hΛ μ hμ j) • W hB hΛ μ hμ j := by
  have hz : z = ∑ j, (bW hB hΛ μ hμ).repr z j • W hB hΛ μ hμ j := by
    conv_lhs => rw [← (bW hB hΛ μ hμ).sum_repr z]
    simp only [bW_apply]
  have hc : ∀ k, (bW hB hΛ μ hμ).repr z k = form (q := q) (q' := q') μ z (W hB hΛ μ hμ k) / rr hB hΛ μ hμ k := by
    intro k
    have := coeff_eq hB hΛ μ hμ (fun j => (bW hB hΛ μ hμ).repr z j) k
    rw [← hz] at this
    rw [this, mul_div_cancel_right₀ _ (rr_ne_zero hB hΛ μ hμ k)]
  conv_lhs => rw [hz]
  simp only [hc]

theorem sq_of_combination (α₁ α₂ α₃ : ℚ) :
    let m := (μ : ℍ[ℚ, a, b]); let ν := (nu hB hΛ μ hμ : ℍ[ℚ, a, b])
    (α₁ • m + α₂ • ν + α₃ • (m * ν)) * (α₁ • m + α₂ • ν + α₃ • (m * ν)) =
      (-(sS q q') * α₁ ^ 2 + dd hB hΛ μ hμ * α₂ ^ 2 + (sS q q' * dd hB hΛ μ hμ) * α₃ ^ 2) • (1 : ℍ[ℚ, a, b]) := by
  intro m ν
  have hμμ : m * m = (-(sS q q')) • (1 : ℍ[ℚ, a, b]) := hmu' μ hμ
  have hνν : ν * ν = (dd hB hΛ μ hμ) • (1 : ℍ[ℚ, a, b]) := nu_nu hB hΛ μ hμ
  have hνμ : ν * m = -(m * ν) := by show (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) * μ = _; rw [mu_nu]; simp
  have hμμx : ∀ x : ℍ[ℚ, a, b], m * (m * x) = (-(sS q q')) • x := mu_mu_mul μ hμ
  have h13 : m * (m * ν) = (-(sS q q')) • ν := hμμx ν
  have h31 : m * ν * m = (sS q q') • ν := by rw [mul_assoc, hνμ, mul_neg, h13, neg_smul, neg_neg]
  have h23 : ν * (m * ν) = (-(dd hB hΛ μ hμ)) • m := by
    rw [← mul_assoc, hνμ, neg_mul, mul_assoc, hνν, mul_smul_comm, mul_one, neg_smul]
  have h32 : m * ν * ν = (dd hB hΛ μ hμ) • m := by rw [mul_assoc, hνν, mul_smul_comm, mul_one]
  have h33 : m * ν * (m * ν) = (sS q q' * dd hB hΛ μ hμ) • (1 : ℍ[ℚ, a, b]) := mu_nu_sq hB hΛ μ hμ
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hμμ, hνν, hνμ, h13, h31, h23, h32, h33, smul_neg,
    smul_smul, neg_smul]
  module

include hB in

theorem dd_pos : 0 < dd hB hΛ μ hμ := by
  have hs := sS_pos (q := q) (q' := q')
  rcases lt_trichotomy (dd hB hΛ μ hμ) 0 with hneg | h0 | hpos
  · exfalso

    have key : ∀ x : ℍ[ℚ, a, b], x.re = 0 → ∀ t : ℚ, x * x = t • (1 : ℍ[ℚ, a, b]) → t ≤ 0 := by
      intro x hx t ht
      have hexp := expansion hB hΛ μ hμ x
      rw [Fin.sum_univ_four] at hexp
      have h0 : form (q := q) (q' := q') μ x (W hB hΛ μ hμ 0) = 0 := by
        simp only [W, Matrix.cons_val_zero, form, sigma_one μ hμ, mul_one]
        simpa [trd] using hx
      rw [h0, zero_div, zero_smul, zero_add] at hexp
      simp only [W, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_three] at hexp
      have hsq := sq_of_combination hB hΛ μ hμ
        (form (q := q) (q' := q') μ x (μ : ℍ[ℚ, a, b]) / rr hB hΛ μ hμ 1)
        (form (q := q) (q' := q') μ x (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) / rr hB hΛ μ hμ 2)
        (form (q := q) (q' := q') μ x ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) / rr hB hΛ μ hμ 3)
      simp only at hsq
      rw [← hexp, ht] at hsq
      set α₁ := form (q := q) (q' := q') μ x (μ : ℍ[ℚ, a, b]) / rr hB hΛ μ hμ 1
      set α₂ := form (q := q) (q' := q') μ x (nu hB hΛ μ hμ : ℍ[ℚ, a, b]) / rr hB hΛ μ hμ 2
      set α₃ := form (q := q) (q' := q') μ x ((μ : ℍ[ℚ, a, b]) * (nu hB hΛ μ hμ : ℍ[ℚ, a, b])) / rr hB hΛ μ hμ 3
      have := congrArg QuaternionAlgebra.re hsq
      simp at this
      rw [this]
      have h1 : -(sS q q') * α₁ ^ 2 ≤ 0 := by nlinarith [sq_nonneg α₁]
      have h2 : dd hB hΛ μ hμ * α₂ ^ 2 ≤ 0 := by nlinarith [sq_nonneg α₂]
      have h3 : sS q q' * dd hB hΛ μ hμ * α₃ ^ 2 ≤ 0 := by nlinarith [sq_nonneg α₃, mul_pos hs (neg_pos.mpr hneg)]
      linarith
    have ha : a ≤ 0 := key ⟨0, 1, 0, 0⟩ rfl a (by ext <;> simp)
    have hb : b ≤ 0 := key ⟨0, 0, 1, 0⟩ rfl b (by ext <;> simp)
    rcases hB.1 with h | h <;> linarith
  · exact absurd h0 (dd_ne_zero hB hΛ μ hμ)
  · exact hpos

theorem rr_pos (i : Fin 4) : 0 < rr hB hΛ μ hμ i := by
  have hs := sS_pos (q := q) (q' := q')
  have hd := dd_pos hB hΛ μ hμ
  fin_cases i <;> simp [rr] <;> positivity

end BasisPart

section Integrality

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))

noncomputable def coord (x : ℍ[ℚ, a, b]) (j : Fin 4) : ℚ :=
  form (q := q) (q' := q') μ x (W hB hΛ μ hμ j) / rr hB hΛ μ hμ j

theorem coord_add (x y : ℍ[ℚ, a, b]) (j : Fin 4) :
    coord hB hΛ μ hμ (x + y) j = coord hB hΛ μ hμ x j + coord hB hΛ μ hμ y j := by
  unfold coord; rw [form_add_left, add_div]

theorem coord_zsmul (n : ℤ) (x : ℍ[ℚ, a, b]) (j : Fin 4) :
    coord hB hΛ μ hμ (n • x) j = n * coord hB hΛ μ hμ x j := by
  unfold coord; rw [← Int.cast_smul_eq_zsmul ℚ, form_smul_left, mul_div_assoc]

theorem coord_zero (j : Fin 4) : coord hB hΛ μ hμ 0 j = 0 := by
  unfold coord form; simp [trd]

theorem expansion' (z : ℍ[ℚ, a, b]) : z = ∑ j, coord hB hΛ μ hμ z j • W hB hΛ μ hμ j :=
  expansion hB hΛ μ hμ z

include hΛ in
theorem exists_denominator :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, ∀ j : Fin 4, ∃ c : ℤ, (c : ℚ) = (N : ℚ) * coord hB hΛ μ hμ x j := by
  classical
  obtain ⟨S, hS⟩ := hΛ.fg
  refine ⟨∏ g ∈ S, ∏ j : Fin 4, (coord hB hΛ μ hμ g j).den, ?_, ?_⟩
  · exact Finset.prod_pos fun g _ => Finset.prod_pos fun j _ => Rat.den_pos _
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro j
    have hdvd : (coord hB hΛ μ hμ g j).den ∣ ∏ g ∈ S, ∏ j : Fin 4, (coord hB hΛ μ hμ g j).den :=
      dvd_trans (Finset.dvd_prod_of_mem (fun j => (coord hB hΛ μ hμ g j).den) (Finset.mem_univ j))
        (Finset.dvd_prod_of_mem (fun g => ∏ j : Fin 4, (coord hB hΛ μ hμ g j).den) hg)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(k : ℤ) * (coord hB hΛ μ hμ g j).num, ?_⟩
    rw [hk]; push_cast
    rw [mul_comm ((coord hB hΛ μ hμ g j).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  | zero => intro j; exact ⟨0, by rw [coord_zero]; simp⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨c₁, h₁⟩ := hx j
    obtain ⟨c₂, h₂⟩ := hy j
    exact ⟨c₁ + c₂, by rw [Int.cast_add, h₁, h₂, coord_add]; ring⟩
  | smul n x _ hx =>
    intro j
    obtain ⟨c, hc⟩ := hx j
    exact ⟨n * c, by rw [Int.cast_mul, hc, coord_zsmul]; ring⟩

end Integrality

end Casimir29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star.Casimir29"

open Casimir29 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ) :
    ∃ (n : ℕ) (w : Fin n → ↥Λ) (m : Fin n → ℕ),
      0 < n ∧ (∀ i, 0 < m i) ∧ (∀ i, (w i : ℍ[ℚ, a, b]) ≠ 0) ∧
      ∀ (G : Type u) [AddCommGroup G] (β : ↥Λ →+ ↥Λ →+ G) (x : ↥Λ),
        ∑ i, m i • β (w i) ⟨(w i : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 x.2⟩ =
        ∑ i, m i • β ⟨(w i : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 (star x).2⟩ (w i) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hs := sS_pos (q := q) (q' := q')
  obtain ⟨N, hN, hint⟩ := exists_denominator hB hO μ hμ
  have hd := dd_pos hB hO μ hμ

  have hnum : 0 < (dd hB hO μ hμ).num := Rat.num_pos.mpr hd
  set p : ℕ := (dd hB hO μ hμ).num.toNat with hp
  set e : ℕ := (dd hB hO μ hμ).den with he
  have hpq : (p : ℚ) = (dd hB hO μ hμ).num := by
    have : ((dd hB hO μ hμ).num.toNat : ℤ) = (dd hB hO μ hμ).num := Int.toNat_of_nonneg hnum.le
    exact_mod_cast this
  have hp0 : 0 < p := by rw [hp]; omega
  have he0 : 0 < e := (dd hB hO μ hμ).den_pos
  have hde : dd hB hO μ hμ * e = p := by rw [hpq, he, Rat.mul_den_eq_num]
  have hsq : ((q * q' : ℕ) : ℚ) = sS q q' := rfl
  have hs0 : 0 < q * q' := Nat.mul_pos (Fact.out : q.Prime).pos (Fact.out : q'.Prime).pos

  set mv : Fin 4 → ℕ := ![q * q' * p * e, p * e, q * q' * e * e, e * e] with hmv
  have hmv_pos : ∀ i, 0 < mv i := by
    intro i
    fin_cases i
    · show 0 < q * q' * p * e; positivity
    · show 0 < p * e; positivity
    · show 0 < q * q' * e * e; positivity
    · show 0 < e * e; positivity
  have hmv_rr : ∀ i, (mv i : ℚ) * rr hB hO μ hμ i = 2 * sS q q' * p * e := by
    intro i
    fin_cases i
    · show ((q * q' * p * e : ℕ) : ℚ) * rr hB hO μ hμ 0 = _
      simp only [rr, Matrix.cons_val_zero, sS]; push_cast; ring
    · show ((p * e : ℕ) : ℚ) * rr hB hO μ hμ 1 = _
      simp only [rr, Matrix.cons_val_one, Matrix.head_cons]; push_cast; ring
    · show ((q * q' * e * e : ℕ) : ℚ) * rr hB hO μ hμ 2 = _
      simp only [rr, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, sS]; push_cast
      linear_combination (2 * (q : ℚ) * (q' : ℚ) * (e : ℚ)) * hde
    · show ((e * e : ℕ) : ℚ) * rr hB hO μ hμ 3 = _
      simp only [rr, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]; push_cast
      linear_combination (2 * sS q q' * (e : ℚ)) * hde
  refine ⟨4, fun i => ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩, fun i => N * mv i, by norm_num,
    fun i => Nat.mul_pos hN (hmv_pos i), ?_, ?_⟩
  ·
    have hμ0 : (μ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h
      have h2 := hmu' μ hμ
      rw [h, zero_mul] at h2
      have h3 := congrArg QuaternionAlgebra.re h2
      simp at h3
      linarith
    have hν0 := nu_ne_zero hB hO μ hμ
    have hμν0 : (μ : ℍ[ℚ, a, b]) * (nu hB hO μ hμ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h
      have h2 := mu_nu_sq hB hO μ hμ
      rw [h, zero_mul] at h2
      have h3 := congrArg QuaternionAlgebra.re h2
      simp at h3
      rcases h3 with h1 | h1
      · linarith
      · exact absurd h1 (dd_ne_zero hB hO μ hμ)
    intro i
    fin_cases i <;> simp [W, hμ0, hν0, hμν0]
  · intro G _ β x

    have hWx : ∀ i, W hB hO μ hμ i * (x : ℍ[ℚ, a, b]) ∈ Λ := fun i => hO.mul_mem (W_mem hB hO μ hμ i) x.2
    have hWx' : ∀ i, W hB hO μ hμ i * (star x : ℍ[ℚ, a, b]) ∈ Λ := fun i => hO.mul_mem (W_mem hB hO μ hμ i) (star x).2
    choose c hc using fun i j => hint _ (hWx i) j
    choose c' hc' using fun i j => hint _ (hWx' i) j

    have key : ∀ (y : ℍ[ℚ, a, b]) (hy : y ∈ Λ) (cc : Fin 4 → ℤ),
        (∀ j, (cc j : ℚ) = (N : ℚ) * coord hB hO μ hμ y j) →
        (N : ℕ) • (⟨y, hy⟩ : ↥Λ) = ∑ j, cc j • (⟨W hB hO μ hμ j, W_mem hB hO μ hμ j⟩ : ↥Λ) := by
      intro y hy cc hcc
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_nsmul, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul_of_tower, Submodule.coe_mk]
      conv_lhs => rw [expansion' hB hO μ hμ y]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, hcc j, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]

    have hcoef : ∀ i j, ((mv i : ℕ) : ℤ) * c i j = ((mv j : ℕ) : ℤ) * c' j i := by
      intro i j
      have hform : form (q := q) (q' := q') μ (W hB hO μ hμ j * (star x : ℍ[ℚ, a, b])) (W hB hO μ hμ i) =
          form (q := q) (q' := q') μ (W hB hO μ hμ i * (x : ℍ[ℚ, a, b])) (W hB hO μ hμ j) := by
        rw [← sigma_coe μ hμ star hstar, form_mul_left μ hμ, sigma_sigma μ hμ, form_symm μ hμ]
      have h1 : ((((mv i : ℕ) : ℤ) * c i j : ℤ) : ℚ) = ((((mv j : ℕ) : ℤ) * c' j i : ℤ) : ℚ) := by
        push_cast
        rw [hc, hc']
        unfold coord
        rw [hform]
        have hri := rr_ne_zero hB hO μ hμ i
        have hrj := rr_ne_zero hB hO μ hμ j
        have hmi := hmv_rr i
        have hmj := hmv_rr j
        field_simp
        linear_combination (form (q := q) (q' := q') μ (W hB hO μ hμ i * (x : ℍ[ℚ, a, b])) (W hB hO μ hμ j)) * hmi -
          (form (q := q) (q' := q') μ (W hB hO μ hμ i * (x : ℍ[ℚ, a, b])) (W hB hO μ hμ j)) * hmj
      exact_mod_cast h1

    have lhs : ∀ i, (N * mv i) • β ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩ ⟨W hB hO μ hμ i * (x : ℍ[ℚ, a, b]), hWx i⟩ =
        ∑ j, (((mv i : ℕ) : ℤ) * c i j) • β ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩ ⟨W hB hO μ hμ j, W_mem hB hO μ hμ j⟩ := by
      intro i
      rw [mul_comm, ← smul_smul, ← map_nsmul, key _ (hWx i) (c i) (hc i), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, ← natCast_zsmul, smul_smul]
    have rhs : ∀ i, (N * mv i) • β ⟨W hB hO μ hμ i * (star x : ℍ[ℚ, a, b]), hWx' i⟩ ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩ =
        ∑ j, (((mv i : ℕ) : ℤ) * c' i j) • β ⟨W hB hO μ hμ j, W_mem hB hO μ hμ j⟩ ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩ := by
      intro i
      rw [mul_comm, ← smul_smul, ← AddMonoidHom.flip_apply β, ← map_nsmul, key _ (hWx' i) (c' i) (hc' i), map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, AddMonoidHom.flip_apply, ← natCast_zsmul, smul_smul]
    simp only [lhs, rhs]
    rw [Finset.sum_comm (f := fun i j => (((mv i : ℕ) : ℤ) * c' i j) • β ⟨W hB hO μ hμ j, W_mem hB hO μ hμ j⟩ ⟨W hB hO μ hμ i, W_mem hB hO μ hμ i⟩)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hcoef i j]

end S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star (solution)
