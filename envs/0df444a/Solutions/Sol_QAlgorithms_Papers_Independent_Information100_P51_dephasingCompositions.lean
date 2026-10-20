-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P51.dephasingCompositions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:30:05.90177+00:00
-- url     : https://prove2.me/submissions/89d21e24-b154-44d5-9522-362103fbc763

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P51

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P51

theorem g52c_kernel_diag (mu : PhaseDensity) (k : ℕ) : dephasingKernel mu k k = 1 := by
  simp only [dephasingKernel, sub_self, mul_zero, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, mu.mass, Complex.ofReal_one]

end QAlgorithms.Papers.Independent.Information100.P51

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P51 in
theorem solution (mu : PhaseDensity) :
    (fun X : FockTraceClass => fockDephasing (bosonicDephasing mu X.val)) =
      (fun X : FockTraceClass => fockDephasing X.val) ∧
    (fun X : FockTraceClass => bosonicDephasing mu (fockDephasing X.val)) =
      (fun X : FockTraceClass => fockDephasing X.val) := by
  constructor
  · funext X; funext k l
    simp only [fockDephasing, bosonicDephasing]
    split_ifs with h
    · subst h; rw [g52c_kernel_diag, mul_one]
    · rfl
  · funext X; funext k l
    simp only [fockDephasing, bosonicDephasing]
    split_ifs with h
    · subst h; rw [g52c_kernel_diag, mul_one]
    · rw [zero_mul]

end
