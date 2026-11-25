-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_card_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:32:31.437124+00:00
-- url     : https://prove2.me/submissions/b39a0305-43f7-4423-a1a1-a9894667f0bf

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_card_pos

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
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r p : ℕ} (hp : p ≤ r) :
    Fintype.card {j : Fin r // ¬ (j : ℕ) < p} = r - p := by
  rw [Fintype.card_subtype_compl, approxB_card_pos hp, Fintype.card_fin]
end ReciprocityTheory.MultiplicativeHeights
