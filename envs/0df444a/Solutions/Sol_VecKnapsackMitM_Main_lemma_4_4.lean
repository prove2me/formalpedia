-- Prove2me | solution 1 for VecKnapsackMitM.Main.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:27:46.756528+00:00
-- url     : https://prove2.me/submissions/a8fd4337-7877-44a8-bedb-af3c5eadb37e

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Geometry

namespace Aux44

open VecKnapsackMitM.Main

lemma maxIdx_eq_max' {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    maxIdx S = (((S.max' hS).val : ℝ) : EReal) := by
  unfold maxIdx
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr (Fin.le_def.mp (Finset.le_max' S i hi)))
  · exact Finset.le_sup (f := fun i : Fin n => (((i.val : ℝ)) : EReal)) (Finset.max'_mem S hS)

lemma minIdx_eq_min' {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    minIdx S = (((S.min' hS).val : ℝ) : EReal) := by
  unfold minIdx
  apply le_antisymm
  · exact Finset.inf_le (f := fun i : Fin n => (((i.val : ℝ)) : EReal)) (Finset.min'_mem S hS)
  · refine Finset.le_inf fun i hi => ?_
    exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr (Fin.le_def.mp (Finset.min'_le S i hi)))

lemma maxIdx_le_sub_one_iff {n : ℕ} (S₁ S₂ : Finset (Fin n)) :
    maxIdx S₁ ≤ minIdx S₂ - 1 ↔ maxIdx S₁ < minIdx S₂ := by
  rcases S₁.eq_empty_or_nonempty with rfl | hS₁
  · have hm₁ : maxIdx (∅ : Finset (Fin n)) = ⊥ := by simp [maxIdx]
    rw [hm₁]
    simp only [bot_le, true_iff]
    rcases S₂.eq_empty_or_nonempty with rfl | hS₂
    · simp [minIdx]
    · rw [minIdx_eq_min' hS₂]
      exact EReal.bot_lt_coe _
  · rw [maxIdx_eq_max' hS₁]
    rcases S₂.eq_empty_or_nonempty with rfl | hS₂
    · have hm₂ : minIdx (∅ : Finset (Fin n)) = ⊤ := by simp [minIdx]
      rw [hm₂]
      have htop : (⊤ : EReal) - 1 = ⊤ := rfl
      rw [htop]
      simp only [le_top, true_iff]
      exact EReal.coe_lt_top _
    · rw [minIdx_eq_min' hS₂]
      have h1 : (1 : EReal) = ((1 : ℝ) : EReal) := rfl
      rw [h1, ← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_lt_coe_iff]
      constructor
      · intro hle
        have hnat : (S₁.max' hS₁).val + 1 ≤ (S₂.min' hS₂).val := by
          exact_mod_cast (by linarith : ((S₁.max' hS₁).val : ℝ) + 1 ≤ ((S₂.min' hS₂).val : ℝ))
        exact Nat.cast_lt.mpr (Nat.lt_of_succ_le hnat)
      · intro hlt
        have hnat : (S₁.max' hS₁).val < (S₂.min' hS₂).val := Nat.cast_lt.mp hlt
        have hle : (S₁.max' hS₁).val + 1 ≤ (S₂.min' hS₂).val := Nat.succ_le_of_lt hnat
        have hreal : ((S₁.max' hS₁).val : ℝ) + 1 ≤ ((S₂.min' hS₂).val : ℝ) := by exact_mod_cast hle
        linarith

end Aux44

open VecKnapsackMitM.Main

theorem solution (d n : ℕ) (hd : 2 ≤ d) (inst : Instance d n) (hinst : inst.Nonneg)
    (S₁ S₂ : Finset (Fin n)) :
    InBox (rangeLo d) (rangeHi inst S₂) (embed inst.toItems S₁) ↔ Matched inst S₁ S₂ := by
  let _ := hd
  constructor
  · intro hbox
    refine ⟨?_, ?_⟩
    · intro t
      have hj := hbox ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
      simp only [rangeLo, rangeHi, embed, t.isLt, ↓reduceDIte] at hj
      have hle : inst.toItems.weight S₁ t ≤ inst.W t - inst.toItems.weight S₂ t :=
        EReal.coe_le_coe_iff.mp hj.2
      linarith
    · have hd_idx := hbox ⟨d, Nat.lt_succ_self d⟩
      simp only [rangeLo, rangeHi, embed, lt_irrefl, ↓reduceDIte, ↓reduceIte] at hd_idx
      exact (Aux44.maxIdx_le_sub_one_iff S₁ S₂).mp hd_idx.2
  · rintro ⟨hw, hidx⟩ j
    by_cases hj : j.val < d
    · simp only [rangeLo, rangeHi, embed, hj, ↓reduceDIte, ↓reduceIte]
      have h0 : (0 : EReal) = ((0 : ℝ) : EReal) := rfl
      rw [h0, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      refine ⟨?_, ?_⟩
      · exact Finset.sum_nonneg fun i _ => hinst.1.2 i ⟨j.val, hj⟩
      · have hwt := hw ⟨j.val, hj⟩
        linarith
    · simp only [rangeLo, rangeHi, embed, hj, ↓reduceDIte, ↓reduceIte]
      exact ⟨bot_le, (Aux44.maxIdx_le_sub_one_iff S₁ S₂).mpr hidx⟩
