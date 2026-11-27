-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.lemma_D_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:06.585132+00:00
-- url     : https://prove2.me/submissions/e7c85466-9bf0-4e16-8039-f87e0de43151

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (U : (Fin m → ℝ) → ℝ)
    (hU : IsConcaveUtility U) (hns : StrictMonoOn U (box m))
    (s : Fin n → Fin m → ℝ) (i : Fin n) (hs : ∀ k, k ≠ i → Strategy I k (s k)) :
    ConcaveOn ℝ (orthant m)
        (fun si : Fin m → ℝ =>
          U (fun j => si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j))) ∧
      ((∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s k j) →
        StrictConcaveOn ℝ (orthant m)
          (fun si : Fin m → ℝ =>
            U (fun j => si j / (si j + ∑ k ∈ Finset.univ.erase i, s k j)))) := by
              have hscalar : ∀ (c x y a b : ℝ), 0 ≤ c → 0 ≤ x → 0 ≤ y →
                  0 < a → 0 < b → a + b = 1 →
                  (a * (x / (x + c)) + b * (y / (y + c)) ≤
                    (a * x + b * y) / (a * x + b * y + c)) ∧
                  (0 < c → x ≠ y → a * (x / (x + c)) + b * (y / (y + c)) <
                    (a * x + b * y) / (a * x + b * y + c)) := by
                intro c x y a b hc hx hy ha hb hab
                have hz : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha.le hx) (mul_nonneg hb.le hy)
                by_cases hc0 : c = 0
                · subst c
                  have hle : a * (x / (x + 0)) + b * (y / (y + 0)) ≤ 1 := by
                    have hxx : x / (x + 0) ≤ 1 := by
                      by_cases h : x = 0
                      · simp [h]
                      · simp [h]
                    have hyy : y / (y + 0) ≤ 1 := by
                      by_cases h : y = 0
                      · simp [h]
                      · simp [h]
                    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hxx),
                      mul_nonneg hb.le (sub_nonneg.mpr hyy)]
                  constructor
                  · by_cases h : a * x + b * y = 0
                    · have hx0 : x = 0 := by nlinarith [mul_nonneg hb.le hy]
                      have hy0 : y = 0 := by nlinarith [mul_nonneg ha.le hx]
                      simp [hx0, hy0]
                    · simpa [h] using hle
                  · intro h
                    linarith
                · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
                  have hxc : x + c ≠ 0 := ne_of_gt (by linarith)
                  have hyc : y + c ≠ 0 := ne_of_gt (by linarith)
                  have hzc : a * x + b * y + c ≠ 0 := ne_of_gt (by linarith)
                  have hid : (a * x + b * y) / (a * x + b * y + c) -
                      (a * (x / (x + c)) + b * (y / (y + c))) =
                      c * a * b * (x - y)^2 / ((x + c) * (y + c) * (a * x + b * y + c)) := by
                    have hb' : b = 1 - a := by linarith
                    subst b
                    field_simp
                    <;> nlinarith [hab]
                  have hden : 0 < (x + c) * (y + c) * (a * x + b * y + c) :=
                    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
                  constructor
                  · have hgap : 0 ≤ c * a * b * (x - y)^2 /
                        ((x + c) * (y + c) * (a * x + b * y + c)) :=
                      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc ha.le) hb.le) (sq_nonneg _)) hden.le
                    linarith
                  · intro _ hxy
                    have hgap : 0 < c * a * b * (x - y)^2 /
                        ((x + c) * (y + c) * (a * x + b * y + c)) :=
                      div_pos (mul_pos (mul_pos (mul_pos hcpos ha) hb)
                        (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))) hden
                    linarith
              let c : Fin m → ℝ := fun j => ∑ k ∈ Finset.univ.erase i, s k j
              have hc : ∀ j, 0 ≤ c j := by
                intro j
                exact Finset.sum_nonneg fun k hk => (hs k (Finset.ne_of_mem_erase hk)).1 j |>.1
              let f : (Fin m → ℝ) → Fin m → ℝ := fun x j => x j / (x j + c j)
              have hconv : Convex ℝ (orthant m) := by
                intro x hx y hy a b ha hb hab j
                exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
              have hfbox : ∀ x ∈ orthant m, f x ∈ box m := by
                intro x hx
                constructor
                · intro j
                  exact div_nonneg (hx j) (add_nonneg (hx j) (hc j))
                · intro j
                  change x j / (x j + c j) ≤ 1
                  by_cases h : x j + c j = 0
                  · simp [h]
                  · exact (div_le_one (lt_of_le_of_ne (add_nonneg (hx j) (hc j)) (Ne.symm h))).2 (by linarith [hc j])
              have hmix : ∀ x ∈ orthant m, ∀ y ∈ orthant m, ∀ a b : ℝ,
                  0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) := by
                intro x hx y hy a b ha hb hab j
                exact (hscalar (c j) (x j) (y j) a b (hc j) (hx j) (hy j) ha hb hab).1
              change ConcaveOn ℝ (orthant m) (fun x => U (f x)) ∧
                ((∀ j, 0 < c j) → StrictConcaveOn ℝ (orthant m) (fun x => U (f x)))
              constructor
              · apply concaveOn_iff_forall_pos.mpr
                refine ⟨hconv, ?_⟩
                intro x hx y hy a b ha hb hab
                have hbox := hU.1.1 (hfbox x hx) (hfbox y hy) ha.le hb.le hab
                exact le_trans (hU.1.2 (hfbox x hx) (hfbox y hy) ha.le hb.le hab)
                  (hU.2.1 hbox (hfbox _ (hconv hx hy ha.le hb.le hab)) (hmix x hx y hy a b ha hb hab))
              · intro hpos
                refine ⟨hconv, ?_⟩
                intro x hx y hy hxy a b ha hb hab
                have hbox := hU.1.1 (hfbox x hx) (hfbox y hy) ha.le hb.le hab
                apply lt_of_le_of_lt (hU.1.2 (hfbox x hx) (hfbox y hy) ha.le hb.le hab)
                apply hns hbox (hfbox _ (hconv hx hy ha.le hb.le hab))
                apply lt_of_le_of_ne (hmix x hx y hy a b ha hb hab)
                intro heq
                apply hxy
                funext j
                by_contra hj
                have hlt := (hscalar (c j) (x j) (y j) a b (hc j) (hx j) (hy j) ha hb hab).2 (hpos j) hj
                have heqj := congrFun heq j
                exact (ne_of_lt hlt) heqj
