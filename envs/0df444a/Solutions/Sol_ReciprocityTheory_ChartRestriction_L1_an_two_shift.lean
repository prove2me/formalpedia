-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.an_two_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:46.166063+00:00
-- url     : https://prove2.me/submissions/8204161c-42be-4e07-a42a-0288c973f02e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgAnTwo
import Theorems.Thm_Formalism_L2_Th1_F_sgStarQuasi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by
  have h := F.sgStarQuasi L ω₀ (z - ω₀ / 2) h0
  have e1 : z - ω₀ / 2 + ω₀ = z + ω₀ / 2 := by ring
  have e2 : (Real.pi : ℂ) * F.herm L (z - ω₀ / 2) ω₀ + (Real.pi : ℂ) * F.herm L ω₀ ω₀ / 2
      = (Real.pi : ℂ) * F.herm L z ω₀ := by
    unfold F.herm; ring
  have e3 : F.semiChar L ω₀ = -1 := by
    unfold F.semiChar; exact if_neg h1
  rw [e1, e2, e3] at h
  rw [h]; ring
end ReciprocityTheory.ChartRestriction.L1
