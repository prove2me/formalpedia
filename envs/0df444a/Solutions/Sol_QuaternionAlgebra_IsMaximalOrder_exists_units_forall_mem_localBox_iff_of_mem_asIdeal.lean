-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_units_forall_mem_localBox_iff_of_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/263871d7-6177-5724-b2e3-1ec4f5c28807

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal.QuaternionAlgebra IsDedekindDomain NumberField"

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re mk_mul_mk imK re_zero re_intCast imJ imI IsMaximalOrder IsDefiniteRamifiedExactlyAt nrd nrd_mk nrd_one exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit"
namespace RamifiedPrincipal
p2m_open "QuaternionAlgebra"

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox (Λ : Submodule ℤ D) {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ}
    (hc : c ∈ v.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem mul_mem_localBox_of {I Λ : Submodule ℤ D} (hmul : ∀ x ∈ I, ∀ y ∈ Λ, x * y ∈ I)
    {x y : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox I v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox I v := by
  have step : ∀ s ∈ {x : D ⊗[ℚ] v.adicCompletion ℚ | ∃ z ∈ I, ∃ c : v.adicCompletion ℚ,
      c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c},
      Submodule.localBox Λ v ≤ (Submodule.localBox I v).comap (AddMonoidHom.mulLeft s) := by
    rintro s ⟨z, hz, c, hc, rfl⟩
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z hz z' hz', c * c', mul_mem hc hc', rfl⟩
  have key : Submodule.localBox I v ≤ (Submodule.localBox I v).comap (AddMonoidHom.mulRight y) := by
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight]
    exact step s hs hy
  exact key hx

end Box

theorem nrd_mul {K : Type*} [CommRing K] {c₁ c₃ : K} (x y : ℍ[K, c₁, c₃]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk, zero_mul, mul_zero, add_zero, sub_zero]
  ring

theorem charZero_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

end QuaternionAlgebra.RamifiedPrincipal

open QuaternionAlgebra.RamifiedPrincipal in
theorem solution
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIΛ : I ≤ Λ)
    (hmul : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    (hfull : ∃ n : ℤ, n ≠ 0 ∧ ∀ μ ∈ Λ, n • μ ∈ I)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ X : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        t ∈ Submodule.localBox I v ↔
          ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * t ∈
            Submodule.localBox Λ v := by
  classical
  haveI := charZero_adicCompletion v
  set K := v.adicCompletion ℚ with hKdef
  set A := algebraMap ℚ K with hAdef

  have hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ≠ 0 → IsUnit x := (hdef.2.2 v).mpr hpv

  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := A a) (d₂ := (0 : K)) (d₃ := A b)
    rfl (map_zero A) rfl (AlgEquiv.refl : ℍ[K, A a, A b] ≃ₐ[K] ℍ[K, A a, A b])
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨A z.re, A z.imI, A z.imJ, A z.imK⟩ : ℍ[K, A a, A b]) := by
    intro z r; rw [hφ]; rfl

  have hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ∈ Submodule.localBox Λ v ↔ nrd (φ x) ∈ v.adicCompletionIntegers ℚ :=
    fun x => QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
      hΛ v hdiv φ hφ' x

  set N : ℍ[ℚ, a, b] ⊗[ℚ] K → K := fun t => nrd (φ t) with hNdef
  have hNmul : ∀ s t, N (s * t) = N s * N t := fun s t => by
    show nrd (φ (s * t)) = nrd (φ s) * nrd (φ t)
    rw [RingEquiv.map_mul, nrd_mul]
  have hN1 : N 1 = 1 := by
    show nrd (φ 1) = 1
    rw [RingEquiv.map_one, nrd_one]
  have hNunit : ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] K, IsUnit t → N t ≠ 0 := by
    rintro _ ⟨u, rfl⟩ h0
    have := hNmul (u : ℍ[ℚ, a, b] ⊗[ℚ] K) ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)
    rw [Units.mul_inv, hN1, h0, zero_mul] at this
    exact one_ne_zero this
  have hNne : ∀ t : ℍ[ℚ, a, b] ⊗[ℚ] K, t ≠ 0 → Valued.v (N t) ≠ 0 := fun t ht =>
    (Valuation.ne_zero_iff _).mpr (hNunit t (hdiv t ht))

  have hle : ∀ t ∈ Submodule.localBox Λ v, Valued.v (N t) ≤ 1 := fun t ht =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp ((hbox t).mp ht)
  have hlog1 : ((1 : WithZero (Multiplicative ℤ))).log = 0 := by
    rw [← WithZero.exp_zero, WithZero.log_exp]

  obtain ⟨n, hn, hnI⟩ := hfull
  set E : Set ℤ := {e | ∃ t ∈ Submodule.localBox I v, t ≠ 0 ∧ (Valued.v (N t)).log = e} with hEdef
  have hEne : E.Nonempty := by

    have hnmem : ((n : ℍ[ℚ, a, b])) ∈ I := by
      have := hnI 1 hΛ.1.one_mem
      rwa [zsmul_one] at this
    have ht₁ : (n : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : K) ∈ Submodule.localBox I v := tmul_mem_localBox v I hnmem (one_mem _)
    have ht₁0 : (n : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : K) ≠ 0 := by
      intro h0
      have h1 : φ ((n : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : K)) = 0 := by rw [h0, RingEquiv.map_zero]
      rw [hφ', one_smul] at h1
      have h2 := congrArg QuaternionAlgebra.re h1
      simp only [QuaternionAlgebra.re_intCast, QuaternionAlgebra.re_zero] at h2
      rw [map_intCast] at h2
      exact hn (Int.cast_eq_zero.mp h2)
    exact ⟨_, _, ht₁, ht₁0, rfl⟩
  have hEbdd : BddAbove E := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, ht, ht0, rfl⟩
    rw [← hlog1, WithZero.log_le_log (hNne t ht0) one_ne_zero]
    exact hle t (localBox_mono v hIΛ ht)
  obtain ⟨t₀, ht₀I, ht₀0, ht₀e⟩ := Int.csSup_mem hEne hEbdd
  have hmax : ∀ t ∈ Submodule.localBox I v, t ≠ 0 → (Valued.v (N t)).log ≤ (Valued.v (N t₀)).log := by
    intro t ht ht0
    rw [ht₀e]
    exact le_csSup hEbdd ⟨t, ht, ht0, rfl⟩

  let X : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ := (hdiv t₀ ht₀0).unit
  have hXval : (X : ℍ[ℚ, a, b] ⊗[ℚ] K) = t₀ := (hdiv t₀ ht₀0).unit_spec
  refine ⟨X, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  ·
    by_cases ht0 : t = 0
    · rw [ht0, mul_zero]; exact zero_mem _
    rw [hbox, HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v (N (((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t)) ≤ 1
    have hXt0 : ((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t ≠ 0 := by
      intro h0
      apply ht0
      have := congrArg (fun s => (X : ℍ[ℚ, a, b] ⊗[ℚ] K) * s) h0
      simpa using this
    have hkey : N (((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t) * N t₀ = N t := by
      rw [← hXval, mul_comm, ← hNmul, ← mul_assoc, Units.mul_inv, one_mul]
    have hlogs : (Valued.v (N (((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t))).log +
        (Valued.v (N t₀)).log = (Valued.v (N t)).log := by
      rw [← WithZero.log_mul (hNne _ hXt0) (hNne _ ht₀0), ← map_mul, hkey]
    have hmax' := hmax t ht ht0
    have hgoal : (Valued.v (N (((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t))).log ≤ 0 := by omega
    rw [← hlog1, WithZero.log_le_log (hNne _ hXt0) one_ne_zero] at hgoal
    exact hgoal
  ·
    have e : t = t₀ * ((((X⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * t)) := by
      rw [← hXval, ← mul_assoc, Units.mul_inv, one_mul]
    rw [e]
    exact mul_mem_localBox_of v hmul ht₀I ht

end

end S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_units_forall_mem_localBox_iff_of_mem_asIdeal (solution)
