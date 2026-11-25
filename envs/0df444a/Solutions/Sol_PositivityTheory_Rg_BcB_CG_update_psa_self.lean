-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.update_psa_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:18.696588+00:00
-- url     : https://prove2.me/submissions/2ce8cee5-6a89-4753-9da3-8760919ff59f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_apply
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {ι : Type} [DecidableEq ι] {X : Type}
variable {Idx : ι → Type}
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (w : ι) (j j' : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) w j' = (Equiv.piSplitAt w Idx).symm (j', J') := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · exact Function.update_self _ _ _
  · funext v
    show Function.update _ w j' (v : ι) = J' v
    rw [Function.update_of_ne v.2, psa_symm_ne]
end PositivityTheory.Rg.BcB.CG
