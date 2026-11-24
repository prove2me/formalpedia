-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.listSub_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:50.607246+00:00
-- url     : https://prove2.me/submissions/f3467a1d-c0a6-4a26-908d-547043266dea

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
theorem _root_.solution (A T : Module.End ℂ V) (h : Commute A T) (L : List ℂ) :
    Commute (L.map fun r => A - algebraMap ℂ _ r).prod T := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commutes r T)
end PositivityTheory.Rg.Cz.ChainP
