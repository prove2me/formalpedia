-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.qdet_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:41.021313+00:00
-- url     : https://prove2.me/submissions/bedf0d96-b074-4b55-9cec-7464a6936871

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ) (Z : A)
    (h : ∀ a b, Commute (E a b) Z) : Commute (qdet E u) Z := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _
end PositivityTheory.Rg.Cz.TA
