-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.bGram_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:02.161675+00:00
-- url     : https://prove2.me/submissions/687193b5-eb35-4d03-896e-ca27041460ed

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) :
    (bGram μ s w).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, bGram, of_apply, Complex.star_def]
  rw [← integral_conj]
  congr 1; funext x
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
