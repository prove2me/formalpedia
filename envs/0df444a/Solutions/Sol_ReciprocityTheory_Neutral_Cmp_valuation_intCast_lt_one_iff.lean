-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.valuation_intCast_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:49.820403+00:00
-- url     : https://prove2.me/submissions/afe3c904-c45e-4d03-8325-438401a2017f

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_Compat_valuation_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (n : ℤ) :
    B.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := fun m =>
    (B.valuation_le_one_iff _).mpr (intCast_mem B m)
  constructor
  · intro hn
    by_contra hpn
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hpn
    have h1 : B.valuation ((a : Ω) * (p : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hp
    have h2 : B.valuation ((b : Ω) * (n : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hn
    have h3 : ((a : Ω) * (p : Ω)) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast hab
    have h4 := B.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
    rw [h3, map_one] at h4
    exact absurd (lt_of_le_of_lt h4 (max_lt h1 h2)) (lt_irrefl 1)
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) hp
end ReciprocityTheory.Neutral.Cmp
