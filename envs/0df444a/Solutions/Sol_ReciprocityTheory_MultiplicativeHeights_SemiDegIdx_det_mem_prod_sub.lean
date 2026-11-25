-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.det_mem_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:03.672154+00:00
-- url     : https://prove2.me/submissions/54b1cfba-e91f-4e52-8c5d-9940cf1a9868

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCB
import Definitions.Def_Lemmata_MiscLemmasR_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_prod_mem_prod_sub

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (T : Matrix (Fin k) (Fin k) K)
    (hT : ∀ i j, T i j ∈ p i) : T.det ∈ ∏ i, p i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_prod_sub p (fun i => Tᵀ (σ i) i) fun i => hT i (σ i)) _
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
