-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.emb_zeta4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:34.458776+00:00
-- url     : https://prove2.me/submissions/b8a90949-74ec-44a0-b2dc-cd59f886a376

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (φ : QI →+* ℂ) :
    ∃ s : ℤ, s ^ 2 = 1 ∧ φ (IsCyclotomicExtension.zeta 4 ℚ QI) = s * Complex.I := by
  have hz := IsCyclotomicExtension.zeta_spec 4 ℚ QI
  have h4 : (φ (IsCyclotomicExtension.zeta 4 ℚ QI)) ^ 4 = 1 := by
    rw [← map_pow, hz.pow_eq_one, map_one]
  have hp : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta 4 ℚ QI)) 4 :=
    hz.map_of_injective φ.injective
  set z := φ (IsCyclotomicExtension.zeta 4 ℚ QI)
  have h2 : z ^ 2 ≠ 1 := by
    intro h
    have := hp.dvd_of_pow_eq_one 2 h
    norm_num at this
  have hsq : z ^ 2 = -1 := by
    have : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
      have : (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
      rw [this, h4, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h2
    · exact eq_neg_of_add_eq_zero_left h
  have hf : (z - Complex.I) * (z + Complex.I) = 0 := by
    have : (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
    rw [this, hsq, Complex.I_sq, sub_self]
  rcases mul_eq_zero.1 hf with h | h
  · exact ⟨1, by norm_num, by rw [sub_eq_zero.1 h]; simp⟩
  · exact ⟨-1, by norm_num, by rw [eq_neg_of_add_eq_zero_left h]; simp⟩
end ReciprocityTheory.MultiplicativeHeights
