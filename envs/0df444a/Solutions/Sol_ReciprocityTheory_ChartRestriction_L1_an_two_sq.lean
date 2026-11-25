-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.an_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:00.156718+00:00
-- url     : https://prove2.me/submissions/3a5381be-46a6-4f90-bb57-f63f42186a04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgAnTwo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_an_two_shift
import Theorems.Thm_Formalism_L2_Th1_F_sgStarAdd


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
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    Complex.exp ((Real.pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by
  have h := F.sgStarAdd L z (ω₀ / 2) hz h1
  rw [an_two_shift L ω₀ h0 h1 z] at h
  linear_combination -h
end ReciprocityTheory.ChartRestriction.L1
