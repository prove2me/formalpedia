-- Prove2me | solution 2 for PositivityTheory.Rg.Cz.KTy.card_filter_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:29.735964+00:00
-- url     : https://prove2.me/submissions/3d2d6c34-0dcc-424d-baa5-dc134a2a6621

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
theorem _root_.solution {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → Prop) [DecidablePred f] :
    (Finset.univ.filter fun a => f (e a)).card = (Finset.univ.filter f).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun b => if f b then 1 else 0)
end PositivityTheory.Rg.Cz.KTy
