-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:16.915005+00:00
-- url     : https://prove2.me/submissions/6aec11e0-93a4-4b34-8883-f402ca3b53d7

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_h_add_right

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (x : Fin r → K) (f : α → Fin r → K) :
    S.h x (∑ j ∈ s, f j) = ∑ j ∈ s, S.h x (f j) := by
  exact map_sum (AddMonoidHom.mk' (S.h x) ((approxB_h_add_right S) x)) f s
end ReciprocityTheory.MultiplicativeHeights
