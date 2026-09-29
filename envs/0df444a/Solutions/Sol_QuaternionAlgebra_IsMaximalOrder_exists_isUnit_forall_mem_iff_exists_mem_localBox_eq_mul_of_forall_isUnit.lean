-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9be3b982-d1c7-571c-a7fa-92db0693cfd7

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField

namespace DivLatPrincipal

local notation "Kv" w => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w

section
variable {K : Type*} [CommRing K] {c₁ c₃ : K}

theorem nrd_mul' (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_one' : QuaternionAlgebra.nrd (1 : ℍ[K, c₁, c₃]) = 1 := by
  rw [show (1 : ℍ[K, c₁, c₃]) = ⟨1, 0, 0, 0⟩ from rfl, QuaternionAlgebra.nrd_mk]; ring

theorem nrd_natCast' (n : ℕ) : QuaternionAlgebra.nrd ((n : ℕ) : ℍ[K, c₁, c₃]) = (n : K) ^ 2 := by
  rw [show ((n : ℕ) : ℍ[K, c₁, c₃]) = ⟨(n : K), 0, 0, 0⟩ by ext <;> simp, QuaternionAlgebra.nrd_mk]; ring
end

variable {a b : ℚ}

theorem exists_coords (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+*
        ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b],
      ∀ (x : ℍ[ℚ, a, b]) (r : Kv w),
        φ (x ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (Kv w) x.re, algebraMap ℚ (Kv w) x.imI,
          algebraMap ℚ (Kv w) x.imJ, algebraMap ℚ (Kv w) x.imK⟩ :
            ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := Kv w) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (Kv w) a) (d₂ := (0 : Kv w)) (d₃ := algebraMap ℚ (Kv w) b) rfl (map_zero _) rfl
    (AlgEquiv.refl (R := Kv w) (A₁ := ℍ[Kv w, algebraMap ℚ (Kv w) a, (0 : Kv w), algebraMap ℚ (Kv w) b]))
  exact ⟨φ, fun x r => by rw [hφ]; rfl⟩

end DivLatPrincipal

open DivLatPrincipal in
open QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    {p : ℕ} [Fact p.Prime] (hpw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal)
    (M : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) (hM0 : ∃ x ∈ M, x ≠ 0)
    (hleft : ∀ d ∈ Submodule.localBox Λ w, ∀ x ∈ M, d * x ∈ M)
    (hbdd : ∃ n : ℕ, ∀ x ∈ M, ((p : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ n * x ∈ Submodule.localBox Λ w) :
    ∃ x₀ ∈ M, IsUnit x₀ ∧ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ∈ M ↔ ∃ d ∈ Submodule.localBox Λ w, x = d * x₀ := by
  classical
  obtain ⟨n, hbdd⟩ := hbdd
  obtain ⟨φ, hφ⟩ := exists_coords (a := a) (b := b) w
  have hmem : ∀ x, x ∈ Submodule.localBox Λ w ↔ QuaternionAlgebra.nrd (φ x) ∈ w.adicCompletionIntegers ℚ :=
    fun x => QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ w hdiv φ hφ x

  let N : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →* w.adicCompletion ℚ :=
    { toFun := fun x => QuaternionAlgebra.nrd (φ x)
      map_one' := by simp only [φ.map_one, nrd_one']
      map_mul' := fun x y => by simp only [φ.map_mul, nrd_mul'] }
  have hNdef : ∀ x, N x = QuaternionAlgebra.nrd (φ x) := fun _ => rfl
  have hNu : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ, N u ≠ 0 ∧ N (↑u⁻¹) = (N u)⁻¹ := by
    intro u
    have h := N.map_mul (u : _) (↑u⁻¹ : _)
    rw [Units.mul_inv, N.map_one] at h
    have h0 : N u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact one_ne_zero h
    exact ⟨h0, ((mul_eq_one_iff_inv_eq₀ h0).mp h.symm).symm⟩
  have hNunit : ∀ x, x ≠ 0 → N x ≠ 0 := by
    intro x hx
    obtain ⟨u, rfl⟩ := hdiv x hx
    exact (hNu u).1

  have hp0 : ((p : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
    have : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have h := (map_ne_zero (algebraMap ℚ (w.adicCompletion ℚ))).mpr this
    rwa [map_natCast] at h
  have hNp : N ((p : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ((p : ℕ) : w.adicCompletion ℚ) ^ 2 := by
    rw [hNdef, map_natCast, nrd_natCast']
  have hbound : ∀ x ∈ M, Valued.v (N x) * Valued.v ((p : ℕ) : w.adicCompletion ℚ) ^ (2 * n) ≤ 1 := by
    intro x hx
    have h1 := (hmem _).1 (hbdd x hx)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← hNdef, map_mul, map_pow, hNp, ← pow_mul, map_mul, map_pow,
      mul_comm] at h1
    exact h1

  have hlog : ∀ x, x ≠ 0 → ∃ z : ℤ, Valued.v (N x) = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro x hx
    have hv : Valued.v (N x) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hNunit x hx)
    exact ⟨Multiplicative.toAdd (WithZero.unzero hv), by simp [WithZero.coe_unzero hv]⟩
  obtain ⟨zp, hzp⟩ : ∃ zp : ℤ, Valued.v ((p : ℕ) : w.adicCompletion ℚ) =
      ((Multiplicative.ofAdd zp : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    have hv : Valued.v ((p : ℕ) : w.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp0
    exact ⟨Multiplicative.toAdd (WithZero.unzero hv), by simp [WithZero.coe_unzero hv]⟩

  let P : ℤ → Prop := fun z => ∃ x ∈ M, x ≠ 0 ∧
    Valued.v (N x) = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hPbdd : ∃ B : ℤ, ∀ z, P z → z ≤ B := by
    refine ⟨-((2 * n : ℕ) : ℤ) * zp, fun z ⟨x, hxM, hx0, hz⟩ => ?_⟩
    have h := hbound x hxM
    rw [hz, hzp, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe,
      ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le, nsmul_eq_mul] at h
    push_cast at h ⊢
    linarith
  obtain ⟨x₁, hx₁M, hx₁0⟩ := hM0
  have hPne : ∃ z, P z := by
    obtain ⟨z, hz⟩ := hlog x₁ hx₁0
    exact ⟨z, x₁, hx₁M, hx₁0, hz⟩
  obtain ⟨z₀, ⟨x₀, hx₀M, hx₀0, hz₀⟩, hmax⟩ := Int.exists_greatest_of_bdd hPbdd hPne
  have hle : ∀ x ∈ M, Valued.v (N x) ≤ Valued.v (N x₀) := by
    intro x hxM
    by_cases hx0 : x = 0
    · have hN0 : N 0 = 0 := by
        rw [hNdef, φ.map_zero, show (0 : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
          algebraMap ℚ (w.adicCompletion ℚ) b]) = ⟨0, 0, 0, 0⟩ from rfl, QuaternionAlgebra.nrd_mk]
        ring
      rw [hx0, hN0, map_zero]
      exact zero_le'
    obtain ⟨z, hz⟩ := hlog x hx0
    rw [hz, hz₀, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
    exact hmax z ⟨x, hxM, hx0, hz⟩
  obtain ⟨u₀, hu₀⟩ := hdiv x₀ hx₀0
  refine ⟨x₀, hx₀M, ⟨u₀, hu₀⟩, fun x => ⟨fun hxM => ?_, ?_⟩⟩
  ·
    refine ⟨x * ↑u₀⁻¹, ?_, by rw [mul_assoc, ← hu₀, Units.inv_mul, mul_one]⟩
    rw [hmem, ← hNdef, N.map_mul, (hNu u₀).2, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    have h0 : Valued.v (N u₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hNu u₀).1
    rw [hu₀] at h0 ⊢
    exact mul_inv_le_one_of_le₀ (hle x hxM) zero_le'
  · rintro ⟨d, hd, rfl⟩
    exact hleft d hd x₀ hx₀M

end S_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit (solution)
