-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.product_translated_catenation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:51:02.047857+00:00
-- url     : https://prove2.me/submissions/e1ecebf2-bae6-4851-88f9-f08bf7638fde

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZF

attribute [local instance] Classical.propDecidable

lemma symp_mul {n : ℕ} {X Y : GroupedRealMatrix n} (hX : IsSymplectic X) (hY : IsSymplectic Y) :
    IsSymplectic (X * Y) := by
  unfold IsSymplectic at *
  rw [Matrix.transpose_mul, show Yᵀ * Xᵀ * canonicalJ n * (X * Y) = Yᵀ * (Xᵀ * canonicalJ n * X) * Y by
    simp only [Matrix.mul_assoc], hX, hY]

theorem main {n : ℕ} (T : ℝ) (hT : 0 < T)
    (phi psi : ℝ → GroupedRealMatrix n) (hp : IsPath phi T) (hq : IsPath psi T)
    (hp0 : phi 0 = 1) (hq0 : psi 0 = 1) :
    FixedHomotopic (fun t => psi t*phi t) (translatedCatenate phi psi T) T := by
  set β : ℝ × ℝ → ℝ := fun x => max 0 ((1 + x.1) * x.2 - x.1 * T)
  set α : ℝ × ℝ → ℝ := fun x => min T ((1 + x.1) * x.2)
  have hβ : Continuous β := by fun_prop
  have hα : Continuous α := by fun_prop
  have mβ : Set.MapsTo β (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 T) (Set.Icc 0 T) := by
    rintro ⟨s, t⟩ ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
    refine ⟨le_max_left _ _, max_le hT.le ?_⟩
    nlinarith
  have mα : Set.MapsTo α (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 T) (Set.Icc 0 T) := by
    rintro ⟨s, t⟩ ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
    exact ⟨le_min hT.le (by nlinarith), min_le_left _ _⟩
  refine ⟨fun x => psi (β x) * phi (α x), ?_, ?_, ?_, ?_⟩
  · exact (hq.1.comp hβ.continuousOn mβ).mul (hp.1.comp hα.continuousOn mα)
  · intro s hs t ht
    exact symp_mul (hq.2 _ (mβ ⟨hs, ht⟩)) (hp.2 _ (mα ⟨hs, ht⟩))
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    refine ⟨?_, ?_⟩
    · simp only [β, α, add_zero, one_mul, zero_mul, sub_zero]
      rw [max_eq_right ht0, min_eq_right ht1]
    · simp only [β, α, translatedCatenate]
      split_ifs with h
      · rw [max_eq_left (by linarith), min_eq_right (by linarith), hq0, Matrix.one_mul]
        ring_nf
      · rw [max_eq_right (by linarith), min_eq_left (by linarith)]
        ring_nf
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    refine ⟨?_, ?_⟩
    · simp only [β, α, mul_zero, zero_sub]
      rw [max_eq_left (by nlinarith), min_eq_right hT.le]
    · simp only [β, α]
      rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith)]
      ring_nf

end X4CZF

theorem solution {n : ℕ} (T : ℝ) (hT : 0 < T)
    (phi psi : ℝ → GroupedRealMatrix n) (hp : IsPath phi T) (hq : IsPath psi T)
    (hp0 : phi 0 = 1) (hq0 : psi 0 = 1) :
    FixedHomotopic (fun t => psi t*phi t) (translatedCatenate phi psi T) T :=
  X4CZF.main T hT phi psi hp hq hp0 hq0
