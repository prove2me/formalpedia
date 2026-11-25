-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_xJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:40.940179+00:00
-- url     : https://prove2.me/submissions/0c0f59c2-9952-44ba-af90-a17233f1fc88

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_sum

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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (j : Fin m) : Deg E 1 (xJ E j) := by
  unfold xJ
  refine Deg.add ?_ (deg_sum _ _ fun i _ => ?_)
  · have := Deg.om (E := E) j (Deg.one (P := Fin m) 0)
    rwa [one_mul] at this
  · have := Deg.perm (E := E) (Equiv.swap i j) (Deg.one (P := Fin m) 1)
    rwa [one_mul] at this
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
