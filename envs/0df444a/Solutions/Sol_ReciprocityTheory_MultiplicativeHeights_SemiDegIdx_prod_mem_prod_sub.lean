-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.prod_mem_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:47.397863+00:00
-- url     : https://prove2.me/submissions/1fb7e998-c344-4c21-b845-d3176a92998a

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (x : Fin k → K) (hx : ∀ i, x i ∈ p i) :
    ∏ i, x i ∈ ∏ i, p i := by
  classical
  suffices h : ∀ s : Finset (Fin k), ∏ i ∈ s, x i ∈ ∏ i ∈ s, p i by exact h Finset.univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a) ih
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
