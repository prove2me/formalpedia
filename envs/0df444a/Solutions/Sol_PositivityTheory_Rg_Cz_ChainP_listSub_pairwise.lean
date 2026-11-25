-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.listSub_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:30:22.851029+00:00
-- url     : https://prove2.me/submissions/68f707ae-d58a-4fd5-876f-5db10c150901

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA

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
open PositivityTheory.Rg.Cz.ChainP
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (A : Module.End ℂ V) (L : List ℂ) :
    (L.map fun r => A - algebraMap ℂ _ r).Pairwise Commute := by
  rw [List.pairwise_map]
  exact List.pairwise_of_forall fun r s =>
    ((Commute.refl A).sub_left (Algebra.commutes r A)).sub_right (Algebra.commutes s _).symm
end PositivityTheory.Rg.Cz.ChainP
