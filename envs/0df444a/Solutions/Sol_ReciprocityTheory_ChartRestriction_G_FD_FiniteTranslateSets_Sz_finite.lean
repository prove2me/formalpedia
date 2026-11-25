-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sz_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:40.722009+00:00
-- url     : https://prove2.me/submissions/78333456-4668-4eb2-a676-77c0d687320e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FiniteTranslateSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
open NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
theorem _root_.solution (T : ℝ) : (Sz T).Finite := by
  refine (Set.finite_Icc (-⌈T⌉) ⌈T⌉).subset ?_
  intro n hn
  have hn' : ((n : ℝ)) ^ 2 ≤ T := hn
  have h1 : |n| ≤ n ^ 2 := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h0 : 1 ≤ |n| := Int.one_le_abs h
      nlinarith [abs_mul_abs_self n, abs_nonneg n]
  have h2 : ((|n| : ℤ) : ℝ) ≤ T := by
    have h4 : ((|n| : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h4 ⊢
    linarith
  have h3 : |n| ≤ ⌈T⌉ := by exact_mod_cast h2.trans (Int.le_ceil T)
  exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩
end ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
