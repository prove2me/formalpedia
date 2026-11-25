-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.one_le_cImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:46.356338+00:00
-- url     : https://prove2.me/submissions/3cd73783-3ea7-4a27-97c1-cf02d8bbc085

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_one_map
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_cImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (C : Submodule (𝓞 K) K) (h1 : 1 ≤ C) : 1 ≤ cImage c C := by
  intro x hx
  rw [mem_cImage]
  exact h1 (mem_one_map c hx)
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
