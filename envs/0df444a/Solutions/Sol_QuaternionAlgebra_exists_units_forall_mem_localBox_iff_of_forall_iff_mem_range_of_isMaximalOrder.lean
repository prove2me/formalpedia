-- Prove2me | solution 1 for QuaternionAlgebra.exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8e990e9e-79b8-5df9-b0a2-9fcbf35f7a20

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder_of_notMem_of_notMem
import Theorems.Thm_QuaternionAlgebra_localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace RedS3

noncomputable abbrev ℓ (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

theorem ℓ_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (ℓ w).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) : (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (ℓ w : ℤ) ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_intCast,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Int.cast_id]
  rfl

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ ℓ w ∣ n := by
  rw [show (n : 𝓞 ℚ) = ((n : ℤ) : 𝓞 ℚ) from (Int.cast_natCast n).symm, intCast_mem_asIdeal_iff, Int.natCast_dvd_natCast]

theorem ℓ_eq_of_prime_mem (w : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : ℓ w = p :=
  (Nat.prime_dvd_prime_iff_eq (ℓ_prime w) hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

theorem eq_of_ℓ_eq {w w' : HeightOneSpectrum (𝓞 ℚ)} (h : ℓ w = ℓ w') : w = w' :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

end RedS3

theorem solution
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (Λ₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∃ u : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ, ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔
          ∃ y ∈ Submodule.localBox Λ₁ w,
            x = (u : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) * y *
              ((u⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) := by
  intro w hwv
  by_cases hrbw : ((rbar : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  · refine ⟨1, fun x => ?_⟩
    rw [QuaternionAlgebra.localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal hrr hB Λ hΛ hH' O hO hdef j hj τ hτ hτc R hRiff Λ₁ hΛ₁ w hrbw]
    constructor
    · intro hx; exact ⟨x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  · have hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro hrw
      apply hwv
      exact RedS3.eq_of_ℓ_eq ((RedS3.ℓ_eq_of_prime_mem w (Fact.out) hrw).trans
        (RedS3.ℓ_eq_of_prime_mem v (Fact.out) hv).symm)
    exact QuaternionAlgebra.exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder_of_notMem_of_notMem hrr hB Λ hΛ hH' O hO hdef j hj τ hτ hτc R hRiff Λ₁ hΛ₁ w hrw hrbw

end S_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder
end P2MW
export P2MW.S_QuaternionAlgebra_exists_units_forall_mem_localBox_iff_of_forall_iff_mem_range_of_isMaximalOrder (solution)
