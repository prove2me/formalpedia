-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.bracket_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:47.598906+00:00
-- url     : https://prove2.me/submissions/cba10431-acf7-4d4a-b8fd-b6a63dd92692

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_sum_castLE
import Theorems.Thm_ReciprocityTheory_AnForm_P_star_mul_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) =
      (sW N hd m v : ℂ) := by
  have hin : ∀ i : Fin N, (∑ k, hd k * ‖zMat N v k i‖ ^ 2) -
      ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) i‖ ^ 2 =
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0 := by
    intro i
    rw [sum_castLE N m hm (fun b => hd b * ‖zMat N v b i‖ ^ 2), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.val < m
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  have hR : ∑ a : Fin m, (hd (Fin.castLE hm a))⁻¹ *
      ((∑ k, hd k * ‖zMat N v k (Fin.castLE hm a)‖ ^ 2) -
        ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) (Fin.castLE hm a)‖ ^ 2) =
      sW N hd m v := by
    simp only [hin]
    rw [sum_castLE N m hm (fun i => (hd i)⁻¹ *
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0), sW]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < m
    · rw [if_pos hi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : m ≤ k.val
      · simp only [hi, hk, and_self, if_true]; ring
      · simp [hk]
    · simp [hi]
  have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [star_mul_mul]
  push_cast at hC ⊢
  exact hC
end ReciprocityTheory.AnForm.P
