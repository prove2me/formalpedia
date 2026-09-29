-- Prove2me | solution 1 for QuaternionAlgebra.exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fa399409-419d-5073-a995-4182aaff7cff

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

namespace PenRt1SIntegral

theorem not_isUnit_natCast_ringOfIntegers_rat (r : ℕ) (hr : r.Prime) : ¬ IsUnit ((r : ℕ) : 𝓞 ℚ) := by
  intro hu
  have h2 := hu.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)
  rw [map_natCast] at h2
  rcases Int.isUnit_iff.mp h2 with h | h
  · exact hr.one_lt.ne' (by exact_mod_cast h)
  · have : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    omega

theorem natCast_ringOfIntegers_rat_ne_zero (r : ℕ) (hr : r.Prime) : ((r : ℕ) : 𝓞 ℚ) ≠ 0 := by
  intro h
  have h2 := congrArg (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) h
  rw [map_natCast, map_zero] at h2
  exact hr.ne_zero (by exact_mod_cast h2)

theorem exists_heightOneSpectrum_natCast_mem (r : ℕ) (hr : r.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have hne : Ideal.span {((r : ℕ) : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_natCast_ringOfIntegers_rat r hr
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hrM : ((r : ℕ) : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hMb : M ≠ ⊥ := fun hb => natCast_ringOfIntegers_rat_ne_zero r hr (by rw [hb] at hrM; exact hrM)
  exact ⟨⟨M, hM.isPrime, hMb⟩, hrM⟩

theorem asIdeal_eq_span_of_natCast_mem (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : v.asIdeal = Ideal.span {((r : ℕ) : 𝓞 ℚ)} := by
  obtain ⟨p, hp, hvp⟩ := IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v
  rw [hvp] at hv ⊢
  have hdvd : ((p : ℕ) : 𝓞 ℚ) ∣ ((r : ℕ) : 𝓞 ℚ) := Ideal.mem_span_singleton.mp hv
  have hdvdZ := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ) hdvd
  rw [map_natCast, map_natCast] at hdvdZ
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (Int.natCast_dvd_natCast.mp hdvdZ)
  rw [hpr]

theorem not_natCast_mem_of_ne (r : ℕ) (hr : r.Prime) (v w : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : w ≠ v) : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hrw
  apply hw
  have h1 := asIdeal_eq_span_of_natCast_mem r hr v hv
  have h2 := asIdeal_eq_span_of_natCast_mem r hr w hrw
  exact HeightOneSpectrum.ext (h2.trans h1.symm)

end PenRt1SIntegral

open PenRt1SIntegral in
theorem solution
    {a₁ b₁ : ℚ} (R₁ O : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁) (hO : O ≤ R₁)
    (r : ℕ) [Fact r.Prime] (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (s : (ℍ[ℚ, a₁, b₁])ˣ) (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (hs₃ : Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
        (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr hℓ))) * sf⁻¹ ∈
      primeHeckeSet O ℓ) :
    ∃ a : ℕ, ((r ^ a : ℕ) : ℚ) • ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₁ := by
  have hr : r.Prime := Fact.out

  set A := ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ with hA
  set dℓ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
        (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr hℓ))) with hdℓ
  have hℓQ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ

  have hdval : (dℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ) • (1 : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [hdℓ, Submodule.val_finiteIdeleDiagonal_apply, Units.coe_map, Units.val_mk0]
    change (algebraMap ℚ ℍ[ℚ, a₁, b₁] (ℓ : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ) • (1 : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul']
    rfl
  have hdinv : ((dℓ⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ)⁻¹ • (1 : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hdval, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hℓQ, one_smul]

  obtain ⟨-, h2, -, -⟩ := (mem_primeHeckeSet_iff O ℓ _).1 hs₃
  have hsfO : (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox O := by
    have hinv : (dℓ * sf⁻¹)⁻¹ = sf * dℓ⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [hinv, Units.val_mul, hdinv, mul_smul_comm, mul_one, smul_smul, mul_inv_cancel₀ hℓQ, one_smul] at h2
    exact h2

  have hmono : Submodule.finiteAdeleBox O ≤ Submodule.finiteAdeleBox R₁ := by
    unfold Submodule.finiteAdeleBox
    exact AddSubgroup.closure_mono fun x ⟨z, hz, c, hc, hx⟩ => ⟨z, hO hz, c, hc, hx⟩
  have hsfR : (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox R₁ := hmono hsfO

  have hloc := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R₁ hR₁.fg hR₁.spanTop
    (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)).1 hsfR

  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_natCast_mem r hr
  refine (QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R₁ hR₁ r v hv
    ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])).1 fun w hw => ?_
  rw [← hs₁ w (not_natCast_mem_of_ne r hr v w hv hw)]
  exact hloc w

end S_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet
end P2MW
export P2MW.S_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet (solution)
