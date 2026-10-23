-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P19.commonCause_zero
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T17:08:03.913697+00:00
-- url     : https://prove2.me/submissions/6cb8facc-6018-45f1-bf40-89740933e28b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

lemma cc_term (x y z : ℝ) :
    x * y * z * Real.log (x * y * z) =
      y * (x * z * Real.log (x * z)) + x * (y * z * Real.log (y * z))
        - x * y * (z * Real.log z) := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  rcases eq_or_ne y 0 with hy | hy
  · simp [hy]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  rw [Real.log_mul (mul_ne_zero hx hy) hz, Real.log_mul hx hy, Real.log_mul hx hz,
    Real.log_mul hy hz]
  ring

lemma lawMap_AL {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ) (hb : IsKernel kb) :
    lawMap (commonCause w ka kb) (fun z => (z.1.1, z.2)) = fun x => ka x.2 x.1 * w x.2 := by
  funext x
  obtain ⟨a, l⟩ := x
  simp only [lawMap, commonCause, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_eq', ← Finset.sum_mul, ← Finset.mul_sum, (hb l).2]

lemma lawMap_BL {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ) (ha : IsKernel ka) :
    lawMap (commonCause w ka kb) (fun z => (z.1.2, z.2)) = fun x => kb x.2 x.1 * w x.2 := by
  funext x
  obtain ⟨b, l⟩ := x
  simp only [lawMap, commonCause, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_eq', ← Finset.sum_mul, (ha l).2]

lemma lawMap_L {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ) (ha : IsKernel ka) (hb : IsKernel kb) :
    lawMap (commonCause w ka kb) Prod.snd = w := by
  funext l
  simp only [lawMap, commonCause, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', ← Finset.sum_mul, ← Finset.mul_sum, (ha l).2, (hb l).2]

lemma sum_ABL {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ) (ha : IsKernel ka) (hb : IsKernel kb) :
    ∑ z, commonCause w ka kb z * Real.log (commonCause w ka kb z) =
      (∑ x : A × L, ka x.2 x.1 * w x.2 * Real.log (ka x.2 x.1 * w x.2)) +
      (∑ y : B × L, kb y.2 y.1 * w y.2 * Real.log (kb y.2 y.1 * w y.2)) -
      ∑ l, w l * Real.log (w l) := by
  simp only [commonCause, cc_term, Fintype.sum_prod_type]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul, (hb l).2, one_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul, (ha l).2, one_mul]
  · have h1 : ∀ a : A, ∑ b : B, ∑ l : L, ka l a * kb l b * (w l * Real.log (w l)) =
        ∑ l : L, ka l a * (w l * Real.log (w l)) := fun a => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, (hb l).2, mul_one]
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul, (ha l).2, one_mul]

theorem commonCause_zero {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ)
    (hw : IsLaw w) (ha : IsKernel ka) (hb : IsKernel kb) :
    extensionClassicalCMI (commonCause w ka kb) = 0 := by
  unfold extensionClassicalCMI shannonNats
  rw [lawMap_AL w ka kb hb, lawMap_BL w ka kb ha, lawMap_L w ka kb ha hb, sum_ABL w ka kb ha hb]
  ring

end

end QAlgorithms.Papers.Independent.Gap48.P19


-- Platform entry point: restates the target verbatim.
namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (5): normalized common-cause laws have zero CMI.
The corrected CMI sign is documented in the module preamble. -/
theorem _root_.solution {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    [Nonempty A] [Nonempty B] [Nonempty L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ)
    (hw : IsLaw w) (ha : IsKernel ka) (hb : IsKernel kb) :
    extensionClassicalCMI (commonCause w ka kb) = 0 := by
  apply @QAlgorithms.Papers.Independent.Gap48.P19.commonCause_zero <;> assumption

end

end QAlgorithms.Papers.Independent.Gap48.P19
