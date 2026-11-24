-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_int_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:06.350855+00:00
-- url     : https://prove2.me/submissions/f9639409-e562-43c6-880d-0ba5efbf4922

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_norm_l_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_int_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  refine le_antisymm (kq_int_le l n) ?_
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  have hc : IsCoprime (l : ℤ) n := by
    first
    | exact (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr h
    | exact (Prime.coprime_iff_not_dvd hp).mpr h
  obtain ⟨a, b, hab⟩ := hc
  have e : (a : ℂ_[l]) * (l : ℂ_[l]) + (b : ℂ_[l]) * (n : ℂ_[l]) = 1 := by exact_mod_cast hab
  have h1 := IsUltrametricDist.norm_add_le_max ((a : ℂ_[l]) * (l : ℂ_[l])) ((b : ℂ_[l]) * (n : ℂ_[l]))
  rw [e, norm_one, norm_mul, norm_mul] at h1
  rcases le_max_iff.mp h1 with h2 | h2
  · exact absurd (h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l a)))
      (not_le.mpr (kq_norm_l_lt l))
  · exact h2.trans (mul_le_of_le_one_left (norm_nonneg _) (kq_int_le l b))
end ReciprocityTheory.ChartRestriction.L1
