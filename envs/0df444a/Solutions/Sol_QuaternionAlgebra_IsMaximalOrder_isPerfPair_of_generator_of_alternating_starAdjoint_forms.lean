-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.isPerfPair_of_generator_of_alternating_starAdjoint_forms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9c9070b0-249e-54c5-9606-1d2c5777ef4c

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_isPerfPair_of_generator_of_alternating_starAdjoint_forms
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

universe u v w

namespace StarForms29

variable {a b : ℚ}

theorem re_mul_comm (x y : ℍ[ℚ, a, b]) : (x * y).re = (y * x).re := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk]; ring

theorem trd_mul_comm (x y : ℍ[ℚ, a, b]) : trd (x * y) = trd (y * x) := by
  simp only [trd, re_mul_comm]

@[scoped simp] theorem trd_star' (x : ℍ[ℚ, a, b]) : trd (star x) = trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]

theorem trd_add' (x y : ℍ[ℚ, a, b]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y; simp [trd]; ring

theorem trd_neg' (x : ℍ[ℚ, a, b]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]

theorem trd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : trd (c • x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]; ring

theorem trd_eq_zero_iff (x : ℍ[ℚ, a, b]) : trd x = 0 ↔ x + star x = 0 := by
  rw [add_star_eq_coe_trd]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have := congrArg QuaternionAlgebra.re h
    simpa using this

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
  simp at h
  subst h
  ext <;> simp

theorem mul_left_cancel_mu {μ : ℍ[ℚ, a, b]} {s : ℚ} (hs : s ≠ 0) (hμ : μ * μ = s • (1 : ℍ[ℚ, a, b]))
    {x y : ℍ[ℚ, a, b]} (h : μ * x = μ * y) : x = y := by
  have : μ * (μ * x) = μ * (μ * y) := by rw [h]
  rw [← mul_assoc, ← mul_assoc, hμ, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul] at this
  exact smul_right_injective _ hs this

section Setup

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)

include hμ in
theorem hmu' : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (-(((q * q' : ℕ) : ℚ))) • (1 : ℍ[ℚ, a, b]) := by
  rw [hμ, neg_smul]

theorem qq_pos : (0 : ℚ) < ((q * q' : ℕ) : ℚ) := by
  have hq := (Fact.out : q.Prime).pos
  have hq' := (Fact.out : q'.Prime).pos
  exact_mod_cast Nat.mul_pos hq hq'

include hμ in
theorem mu_re : (μ : ℍ[ℚ, a, b]).re = 0 :=
  re_eq_zero_of_mul_self (s := -(((q * q' : ℕ) : ℚ))) (by have := qq_pos (q := q) (q' := q'); linarith)
    (hmu' μ hμ)

include hμ in
theorem star_mu : Star.star (μ : ℍ[ℚ, a, b]) = -(μ : ℍ[ℚ, a, b]) :=
  star_eq_neg_of_re_eq_zero (mu_re μ hμ)

include hμ in
theorem trd_mu : trd (μ : ℍ[ℚ, a, b]) = 0 := by
  simp [trd, mu_re μ hμ]

include hμ in
theorem mu_cancel {x y : ℍ[ℚ, a, b]} (h : (μ : ℍ[ℚ, a, b]) * x = (μ : ℍ[ℚ, a, b]) * y) : x = y :=
  mul_left_cancel_mu (s := -(((q * q' : ℕ) : ℚ)))
    (by have := qq_pos (q := q) (q' := q'); intro h0; linarith) (hmu' μ hμ) h

include hμ hstar in
theorem starL_add (x y : ↥Λ) : star (x + y) = star x + star y := by
  apply Subtype.ext
  apply mu_cancel μ hμ
  rw [hstar, Submodule.coe_add, Submodule.coe_add, mul_add, hstar, hstar, StarAddMonoid.star_add, add_mul]

include hμ hstar in
theorem starL_one (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) : star ⟨1, h1⟩ = ⟨1, h1⟩ := by
  apply Subtype.ext
  apply mu_cancel μ hμ
  rw [hstar]; simp

include hμ hstar in
theorem coe_starL_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    (star ⟨(x : ℍ[ℚ, a, b]) * y, h⟩ : ℍ[ℚ, a, b]) = (star y : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) := by
  apply mu_cancel μ hμ
  rw [hstar, Subtype.coe_mk, StarMul.star_mul, mul_assoc, ← hstar x, ← mul_assoc, ← hstar y, mul_assoc]

include hμ hstar in
theorem starL_starL (x : ↥Λ) : star (star x) = x := by
  apply Subtype.ext
  apply mu_cancel μ hμ
  rw [hstar]
  have h := congrArg Star.star (hstar x)
  rw [StarMul.star_mul, StarMul.star_mul, star_star, star_mu μ hμ, mul_neg, neg_mul, neg_inj] at h
  exact h

def tau (z : ℍ[ℚ, a, b]) : ℚ := trd ((μ : ℍ[ℚ, a, b]) * z)

theorem tau_add (x y : ℍ[ℚ, a, b]) : tau μ (x + y) = tau μ x + tau μ y := by
  simp only [tau, mul_add, trd_add']

theorem tau_zsmul (n : ℤ) (x : ℍ[ℚ, a, b]) : tau μ (n • x) = n * tau μ x := by
  simp only [tau, ← Int.cast_smul_eq_zsmul ℚ, mul_smul_comm, trd_smul']

include hμ hstar in

theorem tau_eq_zero_iff (z : ↥Λ) : tau μ (z : ℍ[ℚ, a, b]) = 0 ↔ star z = z := by
  rw [tau, trd_eq_zero_iff, StarMul.star_mul, star_mu μ hμ, mul_neg, ← hstar, ← sub_eq_add_neg, sub_eq_zero]
  constructor
  · intro h; exact Subtype.ext (mu_cancel μ hμ h).symm
  · intro h; rw [h]

include hμ hstar in
theorem tau_star (w : ↥Λ) : tau μ (star w : ℍ[ℚ, a, b]) = -tau μ (w : ℍ[ℚ, a, b]) := by
  simp only [tau]
  rw [hstar, trd_mul_comm, ← trd_star' ((μ : ℍ[ℚ, a, b]) * Star.star (w : ℍ[ℚ, a, b])), StarMul.star_mul, star_star,
    star_mu μ hμ, mul_neg, trd_neg', trd_mul_comm]

include hμ hstar in
theorem tau_star_mul_self (z : ↥Λ) : tau μ ((star z : ℍ[ℚ, a, b]) * (z : ℍ[ℚ, a, b])) = 0 := by
  simp only [tau]

  rw [← mul_assoc, hstar, trd_mul_comm, ← mul_assoc, mul_star_eq_coe_nrd, QuaternionAlgebra.coe_mul_eq_smul,
    trd_smul', trd_mu μ hμ, mul_zero]

include hΛ in
theorem tau_int (z : ↥Λ) : ∃ t : ℤ, (t : ℚ) = tau μ (z : ℍ[ℚ, a, b]) :=
  (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd (hΛ.mul_mem μ.2 z.2)).2

end Setup

section Phi

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)

noncomputable def tauZ (z : ↥Λ) : ℤ := (tau_int hΛ μ z).choose

theorem tauZ_spec (z : ↥Λ) : ((tauZ hΛ μ z : ℤ) : ℚ) = tau μ (z : ℍ[ℚ, a, b]) :=
  (tau_int hΛ μ z).choose_spec

theorem tauZ_add (x y : ↥Λ) : tauZ hΛ μ (x + y) = tauZ hΛ μ x + tauZ hΛ μ y := by
  have : ((tauZ hΛ μ (x + y) : ℤ) : ℚ) = ((tauZ hΛ μ x + tauZ hΛ μ y : ℤ) : ℚ) := by
    rw [Int.cast_add, tauZ_spec, tauZ_spec, tauZ_spec, Submodule.coe_add, tau_add]
  exact_mod_cast this

noncomputable def tauZHom : ↥Λ →+ ℤ where
  toFun := tauZ hΛ μ
  map_zero' := by have := tauZ_add hΛ μ 0 0; simpa using this
  map_add' := tauZ_add hΛ μ

@[scoped simp] theorem tauZHom_apply (z : ↥Λ) : tauZHom hΛ μ z = tauZ hΛ μ z := rfl

include hμ in
theorem tauZ_mu_ne_zero : tauZ hΛ μ μ ≠ 0 := by
  intro h
  have h' := tauZ_spec hΛ μ μ
  rw [h, Int.cast_zero, tau, hmu' μ hμ, trd_smul'] at h'
  have : trd (1 : ℍ[ℚ, a, b]) = 2 := by simp [trd]
  rw [this] at h'
  have := qq_pos (q := q) (q' := q')
  linarith

include hμ in

theorem exists_generator : ∃ z₁ : ↥Λ, tauZ hΛ μ z₁ ≠ 0 ∧ ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z := by
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic (tauZHom hΛ μ).range
  have hmem : ∀ z : ↥Λ, tauZ hΛ μ z ∈ AddSubgroup.closure {d} := fun z => by
    rw [← hd]; exact ⟨z, rfl⟩
  have hdmem : d ∈ (tauZHom hΛ μ).range := by
    rw [hd]; exact AddSubgroup.mem_closure_singleton.mpr ⟨1, one_smul _ _⟩
  obtain ⟨z₁, hz₁⟩ := hdmem
  rw [tauZHom_apply] at hz₁
  refine ⟨z₁, ?_, fun z => ?_⟩
  · intro h0
    have := hmem μ
    rw [← hz₁, h0, AddSubgroup.mem_closure_singleton] at this
    obtain ⟨n, hn⟩ := this
    exact tauZ_mu_ne_zero hΛ μ hμ (by rw [← hn, smul_zero])
  · have := hmem z
    rw [AddSubgroup.mem_closure_singleton] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by rw [← hn, hz₁, smul_eq_mul, mul_comm]⟩

noncomputable def phi0 (z₁ z : ↥Λ) : ℤ := tauZ hΛ μ z / tauZ hΛ μ z₁

theorem mul_phi0 {z₁ : ↥Λ} (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (z : ↥Λ) :
    tauZ hΛ μ z₁ * phi0 hΛ μ z₁ z = tauZ hΛ μ z :=
  Int.mul_ediv_cancel' (hgen z)

theorem phi0_add {z₁ : ↥Λ} (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (x y : ↥Λ) :
    phi0 hΛ μ z₁ (x + y) = phi0 hΛ μ z₁ x + phi0 hΛ μ z₁ y := by
  simp only [phi0, tauZ_add]
  exact Int.add_ediv_of_dvd_left (hgen x)

theorem phi0_self {z₁ : ↥Λ} (h0 : tauZ hΛ μ z₁ ≠ 0) : phi0 hΛ μ z₁ z₁ = 1 :=
  Int.ediv_self h0

include hμ hstar in
theorem phi0_star {z₁ : ↥Λ} (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (w : ↥Λ) :
    phi0 hΛ μ z₁ (star w) = -phi0 hΛ μ z₁ w := by
  have h : tauZ hΛ μ (star w) = -tauZ hΛ μ w := by
    have : ((tauZ hΛ μ (star w) : ℤ) : ℚ) = ((-tauZ hΛ μ w : ℤ) : ℚ) := by
      rw [tauZ_spec, Int.cast_neg, tauZ_spec, tau_star μ hμ star hstar]
    exact_mod_cast this
  simp only [phi0, h]
  exact Int.neg_ediv_of_dvd (hgen w)

include hμ hstar in

theorem phi0_eq_zero_iff {z₁ : ↥Λ} (h0 : tauZ hΛ μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z)
    (z : ↥Λ) : phi0 hΛ μ z₁ z = 0 ↔ star z = z := by
  rw [← tau_eq_zero_iff μ hμ star hstar, ← tauZ_spec hΛ μ, Int.cast_eq_zero, ← mul_phi0 hΛ μ hgen z,
    mul_eq_zero, or_iff_right h0]

include hμ hstar in

theorem factor {N : Type u} [AddCommGroup N] {z₁ : ↥Λ} (h0 : tauZ hΛ μ z₁ ≠ 0)
    (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z)
    (φ : ↥Λ →+ N) (hφ : ∀ z : ↥Λ, star z = z → φ z = 0) (z : ↥Λ) :
    φ z = phi0 hΛ μ z₁ z • φ z₁ := by
  have hw : star (z - phi0 hΛ μ z₁ z • z₁) = z - phi0 hΛ μ z₁ z • z₁ := by
    rw [← phi0_eq_zero_iff hΛ μ hμ star hstar h0 hgen, sub_eq_add_neg, phi0_add hΛ μ hgen, ← neg_zsmul]
    have : phi0 hΛ μ z₁ (-phi0 hΛ μ z₁ z • z₁) = -phi0 hΛ μ z₁ z * phi0 hΛ μ z₁ z₁ := by
      have hsm : ∀ (n : ℕ) (x : ↥Λ), phi0 hΛ μ z₁ ((n : ℤ) • x) = (n : ℤ) * phi0 hΛ μ z₁ x := by
        intro n x
        induction n with
        | zero =>
          have := phi0_add hΛ μ hgen 0 0
          simp only [add_zero] at this
          simp only [Nat.cast_zero, zero_smul, zero_mul]; linarith
        | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, phi0_add hΛ μ hgen, ih]; ring
      obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (phi0 hΛ μ z₁ z)
      ·
        have h1 := phi0_add hΛ μ hgen ((n : ℤ) • z₁) (-(n : ℤ) • z₁)
        rw [← add_smul, add_neg_cancel, zero_smul] at h1
        have h00 : phi0 hΛ μ z₁ (0 : ↥Λ) = 0 := by
          have := phi0_add hΛ μ hgen 0 0; simp only [add_zero] at this; linarith
        rw [h00, hsm] at h1
        rw [hn]; linarith
      · rw [hn, neg_neg, hsm]
    rw [this, phi0_self hΛ μ h0]; ring
  have := hφ _ hw
  rw [map_sub, map_zsmul, sub_eq_zero] at this
  exact this

end Phi

section Forms

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
  {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
  {M : Type v} [AddCommGroup M] [Module R M]
  (ρ : ↥Λ → (M →ₗ[R] M))
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  {ι : Type w} (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
  (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)

include ρ_add in
theorem rho_zero : ρ 0 = 0 := by
  have := ρ_add 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

def theta : ↥Λ →+ M where
  toFun z := ρ z e
  map_zero' := by rw [rho_zero ρ ρ_add, LinearMap.zero_apply]
  map_add' x y := by rw [ρ_add, LinearMap.add_apply]

@[scoped simp] theorem theta_apply (z : ↥Λ) : theta ρ ρ_add e z = ρ z e := rfl

include hbM in
theorem theta_basis (i : ι) : theta ρ ρ_add e (bΛ i) = bM i := (hbM i).symm

include ρ_mul in
theorem theta_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    theta ρ ρ_add e ⟨(x : ℍ[ℚ, a, b]) * y, h⟩ = ρ x (theta ρ ρ_add e y) := by
  simp only [theta_apply, ρ_mul x y h, LinearMap.comp_apply]

omit hΛ μ star in

theorem addHom_ext_basis {N : Type*} [AddCommGroup N] (f g : ↥Λ →+ N) (h : ∀ i, f (bΛ i) = g (bΛ i)) :
    f = g := by
  have : f.toIntLinearMap = g.toIntLinearMap := bΛ.ext fun i => by simpa using h i
  ext z
  exact congrArg (fun (F : ↥Λ →ₗ[ℤ] N) => F z) this

def phiE (E : M →ₗ[R] M →ₗ[R] R) : ↥Λ →+ R := (E e).toAddMonoidHom.comp (theta ρ ρ_add e)

@[scoped simp] theorem phiE_apply (E : M →ₗ[R] M →ₗ[R] R) (z : ↥Λ) : phiE ρ ρ_add e E z = E e (ρ z e) := rfl

include ρ_mul in
theorem formE (E : M →ₗ[R] M →ₗ[R] R) (hst : ∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n))
    (y z w : ↥Λ) (hw : (w : ℍ[ℚ, a, b]) = (star y : ℍ[ℚ, a, b]) * z) :
    E (theta ρ ρ_add e y) (theta ρ ρ_add e z) = phiE ρ ρ_add e E w := by
  have hmem : (star y : ℍ[ℚ, a, b]) * (z : ℍ[ℚ, a, b]) ∈ Λ := hw ▸ w.2
  have hw' : w = ⟨(star y : ℍ[ℚ, a, b]) * z, hmem⟩ := Subtype.ext hw
  rw [phiE_apply, hw', ρ_mul (star y) z hmem, LinearMap.comp_apply, theta_apply, theta_apply, hst]

omit hΛ μ star in
theorem antisymm_of_alt (E : M →ₗ[R] M →ₗ[R] R) (halt : ∀ m : M, E m m = 0) (m n : M) : E m n = -E n m := by
  have h := halt (m + n)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

include hΛ hμ hstar ρ_mul in
theorem phiE_symm_zero (E : M →ₗ[R] M →ₗ[R] R) (halt : ∀ m : M, E m m = 0)
    (hst : ∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) (w : ↥Λ) (hw : star w = w) :
    phiE ρ ρ_add e E w = 0 := by
  set one : ↥Λ := ⟨1, hΛ.one_mem⟩
  have h1 : E (theta ρ ρ_add e one) (theta ρ ρ_add e w) = phiE ρ ρ_add e E w :=
    formE (star := star) (ρ := ρ) (ρ_mul := ρ_mul) (ρ_add := ρ_add) (e := e) E hst one w w
      (by simp only [one, starL_one μ hμ star hstar hΛ.one_mem, one_mul])
  have h2 : E (theta ρ ρ_add e w) (theta ρ ρ_add e one) = phiE ρ ρ_add e E w :=
    formE (star := star) (ρ := ρ) (ρ_mul := ρ_mul) (ρ_add := ρ_add) (e := e) E hst w one w
      (by simp only [one, hw, mul_one])
  have h3 := antisymm_of_alt E halt (theta ρ ρ_add e one) (theta ρ ρ_add e w)
  rw [h1, h2] at h3
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h3)

variable (z₁ : ↥Λ)

noncomputable def wij (i j : ι) : ↥Λ := ⟨(star (bΛ i) : ℍ[ℚ, a, b]) * bΛ j, hΛ.mul_mem (star (bΛ i)).2 (bΛ j).2⟩

noncomputable def gram (i j : ι) : R := ((phi0 hΛ μ z₁ (wij hΛ star bΛ i j) : ℤ) : R)

noncomputable def E0 : M →ₗ[R] M →ₗ[R] R :=
  bM.constr R fun i => bM.constr R fun j => gram hΛ μ star bΛ z₁ i j

theorem E0_basis (i j : ι) : E0 hΛ μ star bΛ bM z₁ (bM i) (bM j) = gram hΛ μ star bΛ z₁ i j := by
  simp only [E0, Module.Basis.constr_basis]

noncomputable def phi0Hom (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) : ↥Λ →+ ℤ where
  toFun := phi0 hΛ μ z₁
  map_zero' := by have := phi0_add hΛ μ hgen 0 0; simpa using this
  map_add' := phi0_add hΛ μ hgen

def lmulStar (c : ↥Λ) : ↥Λ →+ ↥Λ where
  toFun z := ⟨(star c : ℍ[ℚ, a, b]) * z, hΛ.mul_mem (star c).2 z.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [mul_add])

def rmulStar (z : ↥Λ) : ↥Λ →+ ↥Λ where
  toFun y := ⟨(star y : ℍ[ℚ, a, b]) * z, hΛ.mul_mem (star y).2 z.2⟩
  map_zero' := by
    have : star 0 = 0 := by
      have := starL_add μ hμ star hstar 0 0; simpa using this
    exact Subtype.ext (by simp [this])
  map_add' x y := Subtype.ext (by simp [starL_add μ hμ star hstar, add_mul])

include hbM in
theorem gram1 (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (i : ι) (z w : ↥Λ)
    (hw : (w : ℍ[ℚ, a, b]) = (star (bΛ i) : ℍ[ℚ, a, b]) * z) :
    E0 hΛ μ star bΛ bM z₁ (bM i) (theta ρ ρ_add e z) = ((phi0 hΛ μ z₁ w : ℤ) : R) := by
  have key : (E0 hΛ μ star bΛ bM z₁ (bM i)).toAddMonoidHom.comp (theta ρ ρ_add e) =
      (Int.castAddHom R).comp ((phi0Hom hΛ μ z₁ hgen).comp (lmulStar hΛ star (bΛ i))) := by
    apply addHom_ext_basis bΛ
    intro j
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      theta_basis ρ ρ_add bΛ e bM hbM, E0_basis, gram, Int.castAddHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    rfl
  have := congrArg (fun (F : ↥Λ →+ R) => F z) key
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, Int.castAddHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this]
  have hw' : lmulStar hΛ star (bΛ i) z = w := Subtype.ext hw.symm
  rw [hw']
  rfl

include hbM hμ hstar in
theorem gram2 (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (y z w : ↥Λ)
    (hw : (w : ℍ[ℚ, a, b]) = (star y : ℍ[ℚ, a, b]) * z) :
    E0 hΛ μ star bΛ bM z₁ (theta ρ ρ_add e y) (theta ρ ρ_add e z) = ((phi0 hΛ μ z₁ w : ℤ) : R) := by
  have key : ((E0 hΛ μ star bΛ bM z₁).flip (theta ρ ρ_add e z)).toAddMonoidHom.comp (theta ρ ρ_add e) =
      (Int.castAddHom R).comp ((phi0Hom hΛ μ z₁ hgen).comp (rmulStar hΛ μ hμ star hstar z)) := by
    apply addHom_ext_basis bΛ
    intro i
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply,
      theta_basis ρ ρ_add bΛ e bM hbM, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact gram1 hΛ μ star ρ ρ_add bΛ e bM hbM z₁ hgen i z _ rfl
  have := congrArg (fun (F : ↥Λ →+ R) => F y) key
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply,
    Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this]
  have hw' : rmulStar hΛ μ hμ star hstar z y = w := Subtype.ext hw.symm
  rw [hw']
  rfl

end Forms

section Main

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
  {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
  {M : Type v} [AddCommGroup M] [Module R M]
  (ρ : ↥Λ → (M →ₗ[R] M))
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  {ι : Type w} (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
  (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)
  (z₁ : ↥Λ)

include hμ hstar ρ_mul ρ_add hbM in
theorem E0_star (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (x : ↥Λ) (m n : M) :
    E0 hΛ μ star bΛ bM z₁ (ρ x m) n = E0 hΛ μ star bΛ bM z₁ m (ρ (star x) n) := by
  have key : (E0 hΛ μ star bΛ bM z₁).comp (ρ x) = (E0 hΛ μ star bΛ bM z₁).compl₂ (ρ (star x)) := by
    refine LinearMap.ext_basis bM bM fun i j => ?_
    rw [LinearMap.comp_apply, LinearMap.compl₂_apply]
    have hi := (theta_basis ρ ρ_add bΛ e bM hbM i).symm
    have hj := (theta_basis ρ ρ_add bΛ e bM hbM j).symm
    rw [hi, hj, ← theta_mul ρ ρ_mul ρ_add e x (bΛ i) (hΛ.mul_mem x.2 (bΛ i).2),
      ← theta_mul ρ ρ_mul ρ_add e (star x) (bΛ j) (hΛ.mul_mem (star x).2 (bΛ j).2)]
    set w : ↥Λ := ⟨(star (bΛ i) : ℍ[ℚ, a, b]) * ((star x : ℍ[ℚ, a, b]) * bΛ j),
      hΛ.mul_mem (star (bΛ i)).2 (hΛ.mul_mem (star x).2 (bΛ j).2)⟩
    rw [gram2 hΛ μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ hgen _ _ w
        (by simp only [w, coe_starL_mul μ hμ star hstar, mul_assoc]),
      gram2 hΛ μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ hgen _ _ w (by simp only [w])]
  have := congrArg (fun (B : M →ₗ[R] M →ₗ[R] R) => B m n) key
  simpa only [LinearMap.comp_apply, LinearMap.compl₂_apply] using this

include hμ hstar in
theorem E0_flip (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) :
    (E0 hΛ μ star bΛ bM z₁).flip = -E0 hΛ μ star bΛ bM z₁ := by
  refine LinearMap.ext_basis bM bM fun i j => ?_
  rw [LinearMap.flip_apply, LinearMap.neg_apply, LinearMap.neg_apply, E0_basis, E0_basis, gram, gram,
    ← Int.cast_neg, ← phi0_star hΛ μ hμ star hstar hgen]
  congr 2
  apply Subtype.ext
  simp only [wij]
  rw [coe_starL_mul μ hμ star hstar, starL_starL μ hμ star hstar]

include hμ hstar in
theorem E0_alt (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) (m : M) :
    E0 hΛ μ star bΛ bM z₁ m m = 0 := by
  have := congrArg (fun (B : M →ₗ[R] M →ₗ[R] R) => B m m) (E0_flip hΛ μ hμ star hstar bΛ bM z₁ hgen)
  simp only [LinearMap.flip_apply, LinearMap.neg_apply] at this
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp this)

include hμ hstar hbM in

theorem E0_one_gen (h0 : tauZ hΛ μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z) :
    E0 hΛ μ star bΛ bM z₁ (theta ρ ρ_add e ⟨1, hΛ.one_mem⟩) (theta ρ ρ_add e z₁) = 1 := by
  rw [gram2 hΛ μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ hgen ⟨1, hΛ.one_mem⟩ z₁ z₁
    (by rw [starL_one μ hμ star hstar hΛ.one_mem, one_mul]), phi0_self hΛ μ h0, Int.cast_one]

include hμ hstar ρ_mul hbM in

theorem form_eq_smul_E0 (h0 : tauZ hΛ μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛ μ z₁ ∣ tauZ hΛ μ z)
    (E : M →ₗ[R] M →ₗ[R] R) (halt : ∀ m : M, E m m = 0)
    (hst : ∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) :
    E = (phiE ρ ρ_add e E z₁) • E0 hΛ μ star bΛ bM z₁ := by
  have hfac : ∀ z : ↥Λ, phiE ρ ρ_add e E z = ((phi0 hΛ μ z₁ z : ℤ) : R) * phiE ρ ρ_add e E z₁ := fun z => by
    rw [factor hΛ μ hμ star hstar h0 hgen (phiE ρ ρ_add e E) (phiE_symm_zero hΛ μ hμ star hstar ρ ρ_mul ρ_add e E halt hst) z,
      zsmul_eq_mul]
  refine LinearMap.ext_basis bM bM fun i j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, E0_basis, gram,
    ← theta_basis ρ ρ_add bΛ e bM hbM i, ← theta_basis ρ ρ_add bΛ e bM hbM j,
    formE (star := star) (ρ := ρ) (ρ_mul := ρ_mul) (ρ_add := ρ_add) (e := e) E hst (bΛ i) (bΛ j)
      (wij hΛ star bΛ i j) rfl,
    hfac, smul_eq_mul, mul_comm]

end Main

section Arith

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛM : IsMaximalOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)

omit μ star in

theorem star_mem_of_mem (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : Star.star x ∈ Λ := by
  obtain ⟨t, ht⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have hcoe : ((trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, ← Int.cast_smul_eq_zsmul ℚ]; ext <;> simp
  have : Star.star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    rw [← hcoe, ← add_star_eq_coe_trd]; abel
  rw [this]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

include hqq' hB hμ in

theorem exists_tauZ_eq (z₁ : ↥Λ) : ∃ ε : ℤ, tauZ hΛM.1 μ z₁ = ((q * q' : ℕ) : ℤ) * ε := by
  obtain ⟨t, ht⟩ := (QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
    hqq' hB Λ hΛM μ hμ).1 z₁ z₁.2
  refine ⟨t, ?_⟩
  have := tauZ_spec hΛM.1 μ z₁
  rw [tau, ht] at this
  exact_mod_cast this

include hqq' hB hμ hstar in

theorem exists_dual_vector {z₁ : ↥Λ} (h0 : tauZ hΛM.1 μ z₁ ≠ 0)
    (hgen : ∀ z : ↥Λ, tauZ hΛM.1 μ z₁ ∣ tauZ hΛM.1 μ z) (f : ↥Λ →ₗ[ℤ] ℤ) :
    ∃ z : ↥Λ, ∀ (y w : ↥Λ), (w : ℍ[ℚ, a, b]) = (star y : ℍ[ℚ, a, b]) * z → phi0 hΛM.1 μ z₁ w = f y := by
  have hO : IsOrder Λ := hΛM.1
  set s : ℚ := ((q * q' : ℕ) : ℚ) with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact_mod_cast Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : q'.Prime).ne_zero

  obtain ⟨c₀, hc₀, -⟩ := QuaternionAlgebra.IsOrder.existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt
    hB Λ hO f

  have hc₀bar : ∀ x ∈ Λ, ∃ n : ℤ, (n : ℚ) = trd (Star.star c₀ * x) := by
    intro x hx
    refine ⟨f ⟨Star.star x, star_mem_of_mem hO hx⟩, ?_⟩
    rw [hc₀, Subtype.coe_mk, ← trd_star' (Star.star c₀ * x), StarMul.star_mul, star_star, trd_mul_comm]
  have hμc : (μ : ℍ[ℚ, a, b]) * Star.star c₀ ∈ Λ :=
    (QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ hΛM μ hμ (Star.star c₀)).1 hc₀bar
  obtain ⟨ε, hε⟩ := exists_tauZ_eq hqq' hB hΛM μ hμ z₁
  have hε0 : ε ≠ 0 := by rintro rfl; exact h0 (by rw [hε, mul_zero])
  refine ⟨(-ε) • ⟨(μ : ℍ[ℚ, a, b]) * Star.star c₀, hμc⟩, fun y w hw => ?_⟩

  have hmul := mul_phi0 hO μ hgen w
  have hτ : ((tauZ hO μ w : ℤ) : ℚ) = (ε : ℚ) * s * f y := by
    rw [tauZ_spec, tau, hw, ← mul_assoc, hstar, Submodule.coe_smul, Subtype.coe_mk, mul_assoc, mul_smul_comm,
      ← mul_assoc (μ : ℍ[ℚ, a, b]), hmu' μ hμ, smul_mul_assoc, one_mul, ← Int.cast_smul_eq_zsmul ℚ,
      smul_smul, mul_smul_comm, trd_smul', ← trd_star' (Star.star (y : ℍ[ℚ, a, b]) * Star.star c₀), StarMul.star_mul, star_star,
      star_star, ← hc₀ y, hs]
    push_cast; ring
  have : ((((q * q' : ℕ) : ℤ) * ε * phi0 hO μ z₁ w : ℤ) : ℚ) = ((ε * ((q * q' : ℕ) : ℤ) * f y : ℤ) : ℚ) := by
    rw [← hε, hmul, hτ, hs]; push_cast; ring
  have hZ : ((q * q' : ℕ) : ℤ) * ε * phi0 hO μ z₁ w = ε * ((q * q' : ℕ) : ℤ) * f y := by exact_mod_cast this
  have hne : ((q * q' : ℕ) : ℤ) * ε ≠ 0 := by
    refine mul_ne_zero ?_ hε0
    exact_mod_cast Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : q'.Prime).ne_zero
  have : ((q * q' : ℕ) : ℤ) * ε * phi0 hO μ z₁ w = ((q * q' : ℕ) : ℤ) * ε * f y := by rw [hZ]; ring
  exact mul_left_cancel₀ hne this

end Arith

section Perfect

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛM : IsMaximalOrder Λ)
  (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
  (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
  {R : Type u} [CommRing R] [IsDomain R] [CharZero R]
  {M : Type v} [AddCommGroup M] [Module R M]
  (ρ : ↥Λ → (M →ₗ[R] M))
  (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
  (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
  {ι : Type w} [DecidableEq ι] (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
  (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)
  (z₁ : ↥Λ)

include hqq' hB hμ hstar hbM in

theorem exists_dual_in_M (h0 : tauZ hΛM.1 μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛM.1 μ z₁ ∣ tauZ hΛM.1 μ z) (k : ι) :
    ∃ zk : ↥Λ, ∀ i : ι, E0 hΛM.1 μ star bΛ bM z₁ (bM i) (theta ρ ρ_add e zk) = if i = k then 1 else 0 := by
  obtain ⟨zk, hzk⟩ := exists_dual_vector hqq' hB hΛM μ hμ star hstar h0 hgen (bΛ.coord k)
  refine ⟨zk, fun i => ?_⟩
  rw [gram1 hΛM.1 μ star ρ ρ_add bΛ e bM hbM z₁ hgen i zk
      ⟨(star (bΛ i) : ℍ[ℚ, a, b]) * zk, hΛM.1.mul_mem (star (bΛ i)).2 zk.2⟩ rfl,
    hzk (bΛ i) _ rfl, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

include hqq' hB hμ hstar ρ ρ_add e hbM in

theorem E0_bijective (h0 : tauZ hΛM.1 μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛM.1 μ z₁ ∣ tauZ hΛM.1 μ z) :
    Function.Bijective (E0 hΛM.1 μ star bΛ bM z₁) := by
  classical
  have hO : IsOrder Λ := hΛM.1
  choose zk hzk using exists_dual_in_M hqq' hB hΛM μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ h0 hgen

  have hcoordk : ∀ k : ι, (E0 hO μ star bΛ bM z₁).flip (theta ρ ρ_add e (zk k)) = bM.coord k := fun k => by
    refine bM.ext fun i => ?_
    rw [LinearMap.flip_apply, hzk k i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    all_goals (by_cases h : i = k <;> simp [h, Ne.symm h])
  constructor
  ·
    intro m m' h
    refine bM.ext_elem_iff.mpr fun k => ?_
    have := congrArg (fun (g : M →ₗ[R] R) => g (theta ρ ρ_add e (zk k))) h
    rw [← LinearMap.flip_apply (E0 hO μ star bΛ bM z₁), ← LinearMap.flip_apply (E0 hO μ star bΛ bM z₁), hcoordk k] at this
    simpa [Module.Basis.coord_apply] using this
  ·
    intro g
    haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hO.fg
    haveI : Finite ι := Module.Finite.finite_basis bΛ
    haveI : Fintype ι := Fintype.ofFinite ι
    refine ⟨∑ k, g (bM k) • (-(theta ρ ρ_add e (zk k))), ?_⟩
    refine bM.ext fun i => ?_
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply]
    have hanti : ∀ k, E0 hO μ star bΛ bM z₁ (theta ρ ρ_add e (zk k)) (bM i) =
        -E0 hO μ star bΛ bM z₁ (bM i) (theta ρ ρ_add e (zk k)) := fun k =>
      antisymm_of_alt _ (E0_alt hO μ hμ star hstar bΛ bM z₁ hgen) _ _
    simp only [hanti, neg_neg, hzk, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp

include hqq' hB hμ hstar ρ ρ_add e hbM in
theorem E0_isPerfPair (h0 : tauZ hΛM.1 μ z₁ ≠ 0) (hgen : ∀ z : ↥Λ, tauZ hΛM.1 μ z₁ ∣ tauZ hΛM.1 μ z) :
    (E0 hΛM.1 μ star bΛ bM z₁).IsPerfPair := by
  have hb := E0_bijective hqq' hB hΛM μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ h0 hgen
  refine ⟨hb, ?_⟩
  rw [E0_flip hΛM.1 μ hμ star hstar bΛ bM z₁ hgen]
  have : ⇑(-E0 hΛM.1 μ star bΛ bM z₁) = (fun f : M →ₗ[R] R => -f) ∘ ⇑(E0 hΛM.1 μ star bΛ bM z₁) := by
    ext m; simp
  rw [this]
  exact (neg_involutive.bijective).comp hb

end Perfect

end StarForms29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_isPerfPair_of_generator_of_alternating_starAdjoint_forms.StarForms29"

open StarForms29 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ρ : ↥Λ → (M →ₗ[R] M))
    (ρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (ρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ x ∘ₗ ρ y)
    (ρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y)
    {ι : Type w} (bΛ : Module.Basis ι ℤ ↥Λ) (e : M) (bM : Module.Basis ι R M)
    (hbM : ∀ i : ι, bM i = ρ (bΛ i) e)
    (E₀ : M →ₗ[R] M →ₗ[R] R) (h₀alt : ∀ m : M, E₀ m m = 0)
    (h₀star : ∀ (x : ↥Λ) (m n : M), E₀ (ρ x m) n = E₀ m (ρ (star x) n))
    (hgen : ∀ E : M →ₗ[R] M →ₗ[R] R, (∀ m : M, E m m = 0) →
        (∀ (x : ↥Λ) (m n : M), E (ρ x m) n = E m (ρ (star x) n)) → ∃ r : R, E = r • E₀) :
    E₀.IsPerfPair := by
  classical
  have hO : IsOrder Λ := hΛ.1
  obtain ⟨z₁, h0, hgen₁⟩ := exists_generator hO μ hμ
  set Ec := E0 hO μ star bΛ bM z₁ with hEc
  have hEc_alt := E0_alt hO μ hμ star hstar bΛ bM z₁ hgen₁
  have hEc_star := E0_star hO μ hμ star hstar ρ ρ_mul ρ_add bΛ e bM hbM z₁ hgen₁

  set t : R := phiE ρ ρ_add e E₀ z₁ with ht
  have hE₀ : E₀ = t • Ec := form_eq_smul_E0 hO μ hμ star hstar ρ ρ_mul ρ_add bΛ e bM hbM z₁ h0 hgen₁ E₀ h₀alt h₀star
  obtain ⟨s, hs⟩ := hgen Ec hEc_alt hEc_star

  have hts : s * t = 1 := by
    have h1 := E0_one_gen hO μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ h0 hgen₁
    have := congrArg (fun (B : M →ₗ[R] M →ₗ[R] R) => B (theta ρ ρ_add e ⟨1, hO.one_mem⟩) (theta ρ ρ_add e z₁))
      (show Ec = (s * t) • Ec by rw [← smul_smul, ← hE₀, ← hs])
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    rw [h1, mul_one] at this
    exact this.symm
  have htu : IsUnit t := IsUnit.of_mul_eq_one s (by rw [mul_comm]; exact hts)
  have hperf := E0_isPerfPair hqq' hB hΛ μ hμ star hstar ρ ρ_add bΛ e bM hbM z₁ h0 hgen₁

  obtain ⟨u, hu⟩ := htu
  have hsmul_bij : Function.Bijective (fun f : M →ₗ[R] R => t • f) := by
    rw [← hu]
    refine Function.bijective_iff_has_inverse.mpr ⟨fun f => ((u⁻¹ : Rˣ) : R) • f, fun f => ?_, fun f => ?_⟩
    · simp [smul_smul]
    · simp [smul_smul]
  refine ⟨?_, ?_⟩
  · have : ⇑E₀ = (fun f : M →ₗ[R] R => t • f) ∘ ⇑Ec := by
      ext m; rw [hE₀]; rfl
    rw [this]; exact hsmul_bij.comp hperf.bijective_left
  · have : ⇑E₀.flip = (fun f : M →ₗ[R] R => t • f) ∘ ⇑Ec.flip := by
      ext m n; rw [hE₀]; rfl
    rw [this]; exact hsmul_bij.comp hperf.bijective_right

end S_QuaternionAlgebra_IsMaximalOrder_isPerfPair_of_generator_of_alternating_starAdjoint_forms
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_isPerfPair_of_generator_of_alternating_starAdjoint_forms (solution)
