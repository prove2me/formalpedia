-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.fin_append_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:41.485276+00:00
-- url     : https://prove2.me/submissions/d8d6d86c-3ede-4cf4-bfb5-1111a9147955

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan

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
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {α : Type} {k m : ℕ} (b : Fin k → α) (c : Fin m → α) :
    Fin.append b c ∘ finSumFinEquiv = Sum.elim b c := by
  funext i
  cases i <;> simp
end ReciprocityTheory.MultiplicativeHeights.DegAdd
