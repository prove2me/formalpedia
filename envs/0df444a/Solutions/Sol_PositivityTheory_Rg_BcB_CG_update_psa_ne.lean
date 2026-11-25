-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.update_psa_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:45.38627+00:00
-- url     : https://prove2.me/submissions/716605a6-94c9-4849-84a2-7d4adb528661

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_apply
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_self
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
theorem _root_.solution (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) (x : Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) (v : ι) x =
      (Equiv.piSplitAt w Idx).symm (j, Function.update J' v x) := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · show Function.update _ (v : ι) x w = j
    rw [Function.update_of_ne (Ne.symm v.2), psa_symm_self]
  · funext v'
    show Function.update _ (v : ι) x (v' : ι) = Function.update J' v x v'
    by_cases h : v' = v
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Subtype.ext e)), Function.update_of_ne h, psa_symm_ne]
end PositivityTheory.Rg.BcB.CG
