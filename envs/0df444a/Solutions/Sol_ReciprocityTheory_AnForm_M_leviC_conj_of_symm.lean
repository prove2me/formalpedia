-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.leviC_conj_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:44.39458+00:00
-- url     : https://prove2.me/submissions/95e95b1d-1c36-4706-93c8-e07030b3cb8f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a b : Fin e → ℂ) :
    starRingEnd ℂ (leviC H a b) = leviC H b a := by
  simp only [leviC, map_div₀, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hs b a, hs (I • b) (I • a), hs b (I • a), hs (I • b) a]
  push_cast
  ring
end ReciprocityTheory.AnForm.M
