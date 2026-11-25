-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:49.135445+00:00
-- url     : https://prove2.me/submissions/88306e6f-474a-4fc9-ac22-d07dfe0d8e9e

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.IdentityFiltrationBound
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.IdentityFiltrationBound
theorem _root_.solution {x y P Q : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : x ^ 2 ≤ P * y ^ 2 + Q * x * y) : x ≤ (Q + Real.sqrt P) * y := by
  by_contra hc
  push Not at hc
  have hs := Real.sq_sqrt hP
  have hs0 := Real.sqrt_nonneg P
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hQ hs0) hy) hc
  have h1 : Real.sqrt P * y ≤ x := by nlinarith [mul_nonneg hQ hy]
  nlinarith [mul_pos hxpos (sub_pos.2 hc), mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hy)]
end PositivityTheory.CW.IdentityFiltrationBound
