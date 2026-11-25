-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_embVec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:04.965299+00:00
-- url     : https://prove2.me/submissions/da532a59-775d-4ab9-9b39-94fc35699cbd

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_embVec_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    {α : Type*} (s : Finset α) (f : α → Fin r → K) :
    embVec σ (∑ j ∈ s, f j) = ∑ j ∈ s, embVec σ (f j) := by
  exact map_sum (AddMonoidHom.mk' (embVec σ) (approxB_embVec_add σ)) f s
end ReciprocityTheory.MultiplicativeHeights
