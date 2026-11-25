-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.swap_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:22.598836+00:00
-- url     : https://prove2.me/submissions/d2eafc8c-901c-49bc-8acb-10fe167ae804

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution {P : Type} [DecidableEq P] (S : Finset P) (i j : P) (h : i ∈ S ↔ j ∈ S) (q : P) :
    Equiv.swap i j q ∈ S ↔ q ∈ S := by
  rcases eq_or_ne q i with rfl | hi
  · rw [Equiv.swap_apply_left]
    exact h.symm
  rcases eq_or_ne q j with rfl | hj
  · rw [Equiv.swap_apply_right]
    exact h
  · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
end PositivityTheory.Rg.Cz.JMA
