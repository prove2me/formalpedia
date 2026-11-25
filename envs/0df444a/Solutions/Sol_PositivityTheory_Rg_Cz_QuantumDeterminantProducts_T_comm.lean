-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.T_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:46.332532+00:00
-- url     : https://prove2.me/submissions/977b1e4d-c178-44a1-9421-7ba2f6f01013

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet

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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : σ j = j) : Commute (pm σ) (T E u j) := by
  refine Commute.add_right (Algebra.commutes _ _).symm ?_
  have := (hT n M (Fin n) E hE ∅).2.2.2 σ j
  rw [hj] at this
  exact this
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
