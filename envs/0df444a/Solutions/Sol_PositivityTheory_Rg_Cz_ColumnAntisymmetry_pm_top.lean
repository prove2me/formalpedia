-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.pm_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:21.980797+00:00
-- url     : https://prove2.me/submissions/78213a50-9b8b-47ed-a362-1298940d6b30

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti

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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (σ : Equiv.Perm (Fin m)) (top : Fin n) (g : TV n M (Fin m)) :
    pm σ g (fun _ => top) = g (fun _ => top) := rfl
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
