-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.comm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:33.522925+00:00
-- url     : https://prove2.me/submissions/d5e03e82-8c14-417f-8856-1c2a188f46e2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (A X : Module.End ℂ V) (h : Commute A X)
    {ι : Type} (g : ι → ℂ) (L : List ι) : Commute (L.map fun c => A - algebraMap ℂ _ (g c)).prod X := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commute_algebraMap_left _ _)
end PositivityTheory.Rg.Cz.SpecA
