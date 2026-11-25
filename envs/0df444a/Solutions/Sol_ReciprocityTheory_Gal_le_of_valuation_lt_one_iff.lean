-- Prove2me | solution 1 for ReciprocityTheory.Gal.le_of_valuation_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:49.780075+00:00
-- url     : https://prove2.me/submissions/e0d3c6e4-dc06-4aa8-9969-6d70a975498c

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Theorems.Thm_ReciprocityTheory_Gal_exists_den

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A ≤ A' := by
  intro x hx
  have hx' : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs1' : A'.valuation s = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_
    rw [← not_lt, ← h s hs, hs1]
    exact lt_irrefl 1
  have hxt : x = t * s⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one,
    A'.valuation_le_one_iff]
  exact mem_of_isIntegral_int A' ht
end ReciprocityTheory.Gal
