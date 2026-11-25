-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_f_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:12.200785+00:00
-- url     : https://prove2.me/submissions/8ee697bd-7e64-4fa7-996b-d213bc3cdee2

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_monoC_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (a b : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    starRingEnd ℂ (monoC a (r • z)) * monoC b (r • z) =
      (r : ℂ) ^ ((∑ i, a i) + ∑ i, b i) * (starRingEnd ℂ (monoC a z) * monoC b z) := by
  simp only [sphMonom_monoC_smul, map_mul, map_pow, Complex.conj_ofReal]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
