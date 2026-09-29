-- Prove2me | solution 1 for QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f790e920-ccbc-5131-b432-9947dbbbf07d

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range
import Theorems.Thm_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
import Theorems.Thm_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight
import Theorems.Thm_QuaternionAlgebra_not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne
import Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_isMaximalOrder_of_forall_prime_ne_of_range_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem solution
    (p : ℕ) [Fact p.Prime] (O : Type*) [Ring O] [IsDomain O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hrank : Module.finrank ℤ O = 4)
    (hsplit : ∀ ℓ : ℕ, [Fact ℓ.Prime] → ℓ ≠ p →
      Nonempty (ℤ_[ℓ] ⊗[ℤ] O ≃ₐ[ℤ_[ℓ]] Matrix (Fin 2) (Fin 2) ℤ_[ℓ]))
    (hmaxp : ∀ x : O, (∃ t n : ℤ, x * x - t • x + n • (1 : O) = 0 ∧ (p : ℤ) ∣ t ∧ (p : ℤ) ^ 2 ∣ n) →
      ∃ y : O, x = (p : ℤ) • y) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p ∧
      ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsMaximalOrder Λ ∧
        ∃ θ : O →+* ℍ[ℚ, a, b], Function.Injective θ ∧ Set.range θ = (Λ : Set ℍ[ℚ, a, b]) := by
  classical

  obtain ⟨ℓ, hℓp, hℓprime⟩ : ∃ ℓ : ℕ, ℓ ≠ p ∧ ℓ.Prime := by
    obtain ⟨ℓ, hle, hprime⟩ := Nat.exists_infinite_primes (p + 1)
    exact ⟨ℓ, by omega, hprime⟩
  haveI : Fact ℓ.Prime := ⟨hℓprime⟩
  obtain ⟨hdim, hdiv, hcen⟩ :=
    finrank_rat_tensorProduct_eq_four_and_forall_isUnit_and_forall_comm_mem_range O hrank ℓ (hsplit ℓ hℓp)
  obtain ⟨a, b, ha, hb, ⟨e⟩⟩ :=
    exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four (ℚ ⊗[ℤ] O) hdim hdiv hcen

  set θ : O →+* ℍ[ℚ, a, b] := (e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
    (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom with hθdef
  obtain ⟨hθinj, hord⟩ := QuaternionAlgebra.isOrder_toIntSubmodule_range_comp_includeRight O e
  set Λ : Submodule ℤ ℍ[ℚ, a, b] := AddSubgroup.toIntSubmodule θ.range.toAddSubgroup with hΛdef
  have hrangeΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]) := by
    ext x; simp [hΛdef, RingHom.mem_range]

  have hdivQ : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x := by
    intro x hx
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by simpa using congrArg e h0)
    simpa using (hdiv _ hx').map e

  have hsplitQ : ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∉ v.asIdeal →
      ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun v hv =>
    QuaternionAlgebra.not_forall_isUnit_tensorProduct_adicCompletion_of_forall_prime_ne p O hsplit e v
      (by exact_mod_cast hv)
  have hdef := QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit a b p
    Fact.out ha hb hdivQ hsplitQ
  exact ⟨a, b, hdef, Λ,
    QuaternionAlgebra.isMaximalOrder_of_forall_prime_ne_of_range_eq p O hsplit hmaxp θ hθinj Λ hord hrangeΛ,
    θ, hθinj, hrangeΛ⟩

end S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne
end P2MW
export P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_of_forall_prime_ne (solution)
