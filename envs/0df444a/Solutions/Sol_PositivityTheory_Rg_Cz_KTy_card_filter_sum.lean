-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.card_filter_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:33:41.848244+00:00
-- url     : https://prove2.me/submissions/caa92302-4177-47d3-8515-a2a0065e8935

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA

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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution {α β : Type} [Fintype α] [Fintype β] (f : α ⊕ β → Prop) [DecidablePred f] :
    (Finset.univ.filter f).card =
      (Finset.univ.filter fun a => f (.inl a)).card + (Finset.univ.filter fun b => f (.inr b)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
end PositivityTheory.Rg.Cz.KTy
