-- Prove2me | solution 1 for P2M_FltRegular_not_exists_solution__cd5a77927ad8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:24.119854+00:00
-- url     : https://prove2.me/submissions/8d872cb7-a224-4fc0-a3b8-5c60038cafbd

module
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_CaseII_Statement
public import Theorems.Thm_FltRegular_not_exists_solution

set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial
variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open FltRegular
include hp hreg
namespace FltRegular
theorem _root_.solution : ¬∃ (x y z : 𝓞 K), ¬(hζ.toInteger : 𝓞 K) - 1 ∣ y ∧
    (hζ.toInteger : 𝓞 K) - 1 ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z, hm, hz'', rfl⟩ :
      ∃ m z', 1 ≤ m ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
        z = ((hζ.toInteger : 𝓞 K) - 1) ^ m * z' := by
    obtain ⟨m, z', hz'', rfl⟩ :=
      WfDvdMonoid.max_power_factor hz' hζ.zeta_sub_one_prime'.irreducible
    refine ⟨m, z', ?_, hz'', rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [pow_zero, one_mul] at hz
      exact absurd hz hz''
    · exact h
  refine not_exists_solution hp hreg hζ hm ⟨x, y, z, 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]
end FltRegular
