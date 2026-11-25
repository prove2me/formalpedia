-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.cover_QI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:43.460506+00:00
-- url     : https://prove2.me/submissions/c36be856-f25e-4d35-a833-66b49d4c10f5

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_emb_zeta4

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
theorem _root_.solution (φ : QI →+* ℂ) (w : ℂ) : ∃ l : QI, IsIntegralElt l ∧ ‖φ l - w‖ ^ 2 ≤ 1 := by
  obtain ⟨s, hs, he⟩ := emb_zeta4 φ
  have hz := IsCyclotomicExtension.zeta_spec 4 ℚ QI
  have hint : IsIntegral ℤ (IsCyclotomicExtension.zeta 4 ℚ QI) := hz.isIntegral (by norm_num)
  set ζ := IsCyclotomicExtension.zeta 4 ℚ QI with hζ
  set a : ℤ := round w.re with ha_def
  set b : ℤ := round w.im with hb_def
  refine ⟨(a : QI) + ((s * b : ℤ) : QI) * ζ, ?_, ?_⟩
  · refine ⟨(a : 𝓞 QI) + ((s * b : ℤ) : 𝓞 QI) * ⟨ζ, hint⟩, ?_⟩
    simp only [map_add, map_mul, map_intCast]
    rfl
  · have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
    have h1 : φ ((a : QI) + ((s * b : ℤ) : QI) * ζ) = (a : ℂ) + (b : ℂ) * Complex.I := by
      rw [map_add, map_mul, map_intCast, map_intCast, he]
      push_cast
      linear_combination (b : ℂ) * Complex.I * hs'
    rw [h1]
    have hre : ((a : ℂ) + (b : ℂ) * Complex.I - w).re = (a : ℝ) - w.re := by simp
    have him : ((a : ℂ) + (b : ℂ) * Complex.I - w).im = (b : ℝ) - w.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have ha := abs_sub_round w.re
    have hb := abs_sub_round w.im
    rw [abs_le] at ha hb
    nlinarith [ha.1, ha.2, hb.1, hb.2]
end ReciprocityTheory.MultiplicativeHeights
