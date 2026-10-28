-- Prove2me | solution 1 for StatComplexityDM.MAB.ber_family_is_hard
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:32:02.599244+00:00
-- url     : https://prove2.me/submissions/1d51ce69-c948-4414-a988-17cd596d7106

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_HardFamily
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

open FoundationsRL.GeneralDM

namespace Aux_berhard
open StatComplexityDM.MAB

lemma fM_ber (A : ℕ) (m : Fin A → Bool → ℝ) (q : ℝ) (π : Fin A) (h : m π = ber q) :
    fM berRew m π = q := by
  unfold fM
  rw [h]
  simp [Fintype.sum_bool, ber, berRew]

lemma sq_diff_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hcs : c ≤ (Real.sqrt a + Real.sqrt b) ^ 2) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / c := by
  rw [le_div_iff₀ hc]
  have h1 : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 = (a - b) ^ 2 := by
    have := Real.sq_sqrt ha
    have := Real.sq_sqrt hb
    nlinarith
  calc (Real.sqrt a - Real.sqrt b) ^ 2 * c
      ≤ (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = (a - b) ^ 2 := h1

lemma isDist_ber (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : StatComplexityDM.LowerBound.IsDist (ber q) := by
  refine ⟨fun y => ?_, ?_⟩
  · unfold ber; split_ifs <;> linarith
  · simp [Fintype.sum_bool, ber]

end Aux_berhard

open StatComplexityDM.MAB in
theorem solution (A : ℕ) (hA : 2 ≤ A) (piStar : (Fin A → Bool → ℝ) → Fin A)
    (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel berRew piStar) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 2) :
    IsHardFamily (bernoulliBandits A) berRew piStar (fun _ => ber (1 / 2))
      (berFamily A Δ) Δ (3 * Δ ^ 2) 0 := by
  have hval : ∀ i π, fM berRew (berFamily A Δ i) π = 1 / 2 + Δ * (if π = i then 1 else 0) :=
    fun i π => Aux_berhard.fM_ber A _ _ π rfl
  have hstar : ∀ i, fM berRew (berFamily A Δ i) (piStar (berFamily A Δ i)) = 1 / 2 + Δ := by
    intro i
    have hs := hpiStar (berFamily A Δ i) i
    rw [hval, hval] at hs
    rw [hval]
    simp only [if_pos rfl] at hs
    split_ifs at hs ⊢ <;> linarith
  have hfamM : ∀ i, berFamily A Δ i ∈ bernoulliBandits A := by
    intro i π
    apply Aux_berhard.isDist_ber
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  refine ⟨fun m hm => hm, fun m _ π => hpiStar m π, ?_, hfamM, hA, ?_, ?_⟩
  · intro π
    exact Aux_berhard.isDist_ber _ (by norm_num) (by norm_num)
  · refine ⟨fun i π => if π = i then 1 else 0, ?_, ?_, ?_⟩
    · intro i π; dsimp only; split_ifs <;> norm_num
    · intro π
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      have : (2:ℝ) ≤ A := by exact_mod_cast hA
      linarith
    · intro i π
      dsimp only
      rw [hstar, hval]
      split_ifs <;> linarith
  · refine ⟨fun i π => if π = i then 1 else 0, ?_, ?_, ?_⟩
    · intro i π; dsimp only; split_ifs <;> norm_num
    · intro π
      rw [Finset.sum_ite_eq]
      simp
    · intro i π
      unfold hellingerSq berFamily ber
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      by_cases h : π = i
      · simp only [h, if_true, mul_one, add_zero]
        have hs2 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
        have hss : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
        have t1 := Aux_berhard.sq_diff_le (1 / 2 + Δ) (1 / 2) 2 (by linarith) (by norm_num)
          (by norm_num) (by
            have : Real.sqrt (1 / 2) ≤ Real.sqrt (1 / 2 + Δ) := Real.sqrt_le_sqrt (by linarith)
            nlinarith)
        have t2 := Aux_berhard.sq_diff_le (1 - (1 / 2 + Δ)) (1 - 1 / 2) (1 / 2) (by linarith)
          (by norm_num) (by norm_num) (by
            have : 0 ≤ Real.sqrt (1 - (1 / 2 + Δ)) := Real.sqrt_nonneg _
            have e : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
            rw [e]
            nlinarith)
        have e1 : (1 / 2 + Δ - 1 / 2) ^ 2 / 2 = Δ ^ 2 / 2 := by ring
        have e2 : (1 - (1 / 2 + Δ) - (1 - 1 / 2)) ^ 2 / (1 / 2) = 2 * Δ ^ 2 := by ring
        rw [e1] at t1
        rw [e2] at t2
        nlinarith [sq_nonneg Δ]
      · simp only [h, if_false, mul_zero, add_zero, sub_self]
        norm_num
