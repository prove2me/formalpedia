-- Prove2me | solution 1 for PositivityTheory.KReal.sum_upd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:56.530864+00:00
-- url     : https://prove2.me/submissions/503f15d1-5db8-4c73-8b5a-796ff556cc6b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
import Theorems.Thm_PositivityTheory_KReal_updInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
namespace PositivityTheory.KReal
theorem _root_.solution {β : Type} [AddCommMonoid β] (s : J) (g : (J → I) → I → β) :
    ∑ w, ∑ j, g w j = ∑ w, ∑ j, g (Function.update w s j) (w s) := by
  calc ∑ w, ∑ j, g w j = ∑ x : (J → I) × I, g x.1 x.2 := (Fintype.sum_prod_type' g).symm
    _ = ∑ x : (J → I) × I, g (Function.update x.1 s x.2) (x.1 s) :=
        (Equiv.sum_comp (Function.Involutive.toPerm _ (PositivityTheory.KReal.updInv s))
          (fun x => g x.1 x.2)).symm
    _ = ∑ w, ∑ j, g (Function.update w s j) (w s) :=
        Fintype.sum_prod_type' (fun w j => g (Function.update w s j) (w s))
end PositivityTheory.KReal
