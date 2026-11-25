-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.prod_zpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:27.020482+00:00
-- url     : https://prove2.me/submissions/6c314d6c-8e57-48cd-8cb4-71cf74cd73ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] {y : K} (hy : y ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, y ^ f i = y ^ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hy]
end ReciprocityTheory.ChartRestriction.TR.Weyl
