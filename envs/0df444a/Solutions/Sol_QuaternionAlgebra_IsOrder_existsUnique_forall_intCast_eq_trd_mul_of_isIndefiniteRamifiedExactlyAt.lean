-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ce8114be-3512-510a-af9a-7ed839895e94

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra IsDedekindDomain NumberField

namespace TrdDual

variable {a b : ℚ}

theorem trd_mul_eq (c x : ℍ[ℚ, a, b]) :
    trd (c * x) = 2 * (c.re * x.re + a * c.imI * x.imI + b * c.imJ * x.imJ - a * b * c.imK * x.imK) := by
  obtain ⟨c₀, c₁, c₂, c₃⟩ := c
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [mk_mul_mk, trd]
  ring

def pairing : ℍ[ℚ, a, b] →ₗ[ℚ] ℍ[ℚ, a, b] →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun c x => trd (c * x))
    (fun c c' x => by
      obtain ⟨c₀, c₁, c₂, c₃⟩ := c; obtain ⟨d₀, d₁, d₂, d₃⟩ := c'; obtain ⟨x₀, x₁, x₂, x₃⟩ := x
      simp only [trd, mk_add_mk, mk_mul_mk]; ring)
    (fun r c x => by
      obtain ⟨c₀, c₁, c₂, c₃⟩ := c; obtain ⟨x₀, x₁, x₂, x₃⟩ := x
      simp only [trd, smul_mk, mk_mul_mk, smul_eq_mul]; ring)
    (fun c x x' => by
      obtain ⟨c₀, c₁, c₂, c₃⟩ := c; obtain ⟨d₀, d₁, d₂, d₃⟩ := x'; obtain ⟨x₀, x₁, x₂, x₃⟩ := x
      simp only [trd, mk_add_mk, mk_mul_mk]; ring)
    (fun r c x => by
      obtain ⟨c₀, c₁, c₂, c₃⟩ := c; obtain ⟨x₀, x₁, x₂, x₃⟩ := x
      simp only [trd, smul_mk, mk_mul_mk, smul_eq_mul]; ring)

@[scoped simp] theorem pairing_apply (c x : ℍ[ℚ, a, b]) : pairing c x = trd (c * x) := rfl

theorem pairing_injective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Injective (pairing (a := a) (b := b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h0 := congrArg (fun f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ => f ⟨1, 0, 0, 0⟩) hc
  have h1 := congrArg (fun f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ => f ⟨0, 1, 0, 0⟩) hc
  have h2 := congrArg (fun f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ => f ⟨0, 0, 1, 0⟩) hc
  have h3 := congrArg (fun f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ => f ⟨0, 0, 0, 1⟩) hc
  simp only [pairing_apply, trd_mul_eq, LinearMap.zero_apply] at h0 h1 h2 h3
  obtain ⟨c₀, c₁, c₂, c₃⟩ := c
  simp only at h0 h1 h2 h3
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  ext
  · simpa using h0
  · simpa [ha] using h1
  · simpa [hb] using h2
  · simpa [ha, hb] using h3

theorem pairing_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (pairing (a := a) (b := b)) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp (pairing_injective ha hb)
  rw [QuaternionAlgebra.finrank_eq_four]
  exact ((Subspace.dual_finrank_eq (K := ℚ) (V := ℍ[ℚ, a, b])).trans (QuaternionAlgebra.finrank_eq_four a 0 b)).symm

theorem eq_of_forall_trd_mul_eq (ha : a ≠ 0) (hb : b ≠ 0) {S : Set ℍ[ℚ, a, b]} (hS : Submodule.span ℚ S = ⊤)
    {c c' : ℍ[ℚ, a, b]} (h : ∀ x ∈ S, trd (c * x) = trd (c' * x)) : c = c' := by
  apply pairing_injective ha hb
  refine LinearMap.ext_on hS fun x hx => ?_
  simpa using h x hx

theorem prime_natCast_ringOfIntegers {p : ℕ} (hp : p.Prime) : _root_.Prime (p : 𝓞 ℚ) := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
  rw [this]
  exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ

def placeOfPrime (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(p : 𝓞 ℚ)},
    (Ideal.span_singleton_prime (prime_natCast_ringOfIntegers hp).ne_zero).mpr (prime_natCast_ringOfIntegers hp), by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero⟩

theorem natCast_mem_placeOfPrime (p : ℕ) (hp : p.Prime) : ((p : ℕ) : 𝓞 ℚ) ∈ (placeOfPrime p hp).asIdeal :=
  Ideal.subset_span (Set.mem_singleton _)

theorem ne_zero_and_ne_zero_of_isIndefiniteRamifiedExactlyAt {p₁ p₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b p₁ p₂) : a ≠ 0 ∧ b ≠ 0 := by
  have hdiv := (hB.2 (placeOfPrime p₁ Fact.out)).mpr (Or.inl (natCast_mem_placeOfPrime p₁ Fact.out))
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hdiv
  constructor
  · intro ha0
    have h := hdiv 0 1 0 0 (by rw [ha0]; push_cast; ring)
    exact one_ne_zero h.2.1
  · intro hb0
    have h := hdiv 0 0 1 0 (by rw [hb0]; push_cast; ring)
    exact one_ne_zero h.2.2.1

theorem span_range_mk_eq_top {Λ : Submodule ℤ ℍ[ℚ, a, b]} (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b])
    (hBΛ : ∀ i, B i ∈ Λ) (hspan : Submodule.span ℤ (Set.range B) = Λ) :
    Submodule.span ℤ (Set.range (fun i => (⟨B i, hBΛ i⟩ : ↥Λ))) = ⊤ := by
  apply Submodule.map_injective_of_injective (f := Λ.subtype) (Submodule.injective_subtype Λ)
  rw [Submodule.map_subtype_top, Submodule.map_span]
  conv_rhs => rw [← hspan]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨⟨B i, hBΛ i⟩, ⟨i, rfl⟩, rfl⟩

theorem exists_forall_apply_eq_trd (ha : a ≠ 0) (hb : b ≠ 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (f : ↥Λ →ₗ[ℤ] ℤ) : ∃ c : ℍ[ℚ, a, b], ∀ x : ↥Λ, ((f x : ℤ) : ℚ) = trd (c * (x : ℍ[ℚ, a, b])) := by
  obtain ⟨B, hBΛ, hspan⟩ := hΛ.exists_basis_span_eq
  set F : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ := B.constr ℚ (fun i => ((f ⟨B i, hBΛ i⟩ : ℤ) : ℚ)) with hF
  obtain ⟨c, hc⟩ := pairing_surjective ha hb F
  refine ⟨c, fun x => ?_⟩
  have hFc : ∀ y, trd (c * y) = F y := fun y => by rw [← pairing_apply, hc]
  rw [hFc]

  set g : ↥Λ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap.comp f with hg
  set h : ↥Λ →ₗ[ℤ] ℚ := (F.restrictScalars ℤ).comp (Λ.subtype.restrictScalars ℤ) with hh
  have hgh : g = h := by
    refine LinearMap.ext_on (span_range_mk_eq_top B hBΛ hspan) ?_
    rintro _ ⟨i, rfl⟩
    simp only [hg, hh, LinearMap.coe_comp, Function.comp_apply, AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom,
      LinearMap.coe_restrictScalars, Submodule.subtype_apply, hF, Module.Basis.constr_basis]
  have := congrArg (fun φ : ↥Λ →ₗ[ℤ] ℚ => φ x) hgh
  simpa [hg, hh] using this

theorem unique_of_forall_apply_eq_trd (ha : a ≠ 0) (hb : b ≠ 0) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {c c' : ℍ[ℚ, a, b]} (h : ∀ x ∈ Λ, trd (c * x) = trd (c' * x)) : c = c' :=
  eq_of_forall_trd_mul_eq ha hb hΛ.spanTop h

end TrdDual
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt.TrdDual"

open TrdDual in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (f : ↥Λ →ₗ[ℤ] ℤ) :
    ∃! c : ℍ[ℚ, a, b], ∀ y : ↥Λ, ((f y : ℤ) : ℚ) = trd (c * (y : ℍ[ℚ, a, b])) := by
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero_of_isIndefiniteRamifiedExactlyAt hB
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_trd ha hb hΛ f
  refine ⟨c, hc, fun c' hc' => ?_⟩
  refine unique_of_forall_apply_eq_trd ha hb hΛ fun x hx => ?_
  rw [← hc' ⟨x, hx⟩, ← hc ⟨x, hx⟩]

end S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_existsUnique_forall_intCast_eq_trd_mul_of_isIndefiniteRamifiedExactlyAt (solution)
