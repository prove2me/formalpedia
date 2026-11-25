-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:41.491842+00:00
-- url     : https://prove2.me/submissions/5f972619-93b4-421a-ae8a-6ff8c8253760

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_xJ

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
theorem _root_.solution (i j : Fin m) (c : Prop) [Decidable c] :
    Deg E (if c then 1 else 0) (if c then xJ E i - xJ E j + 1 else 1) := by
  split_ifs
  · refine Deg.add ?_ (Deg.one 1)
    rw [sub_eq_add_neg]
    refine Deg.add (deg_xJ i) ?_
    have h1 := Deg.smul (-1 : ℂ) (deg_xJ (E := E) j)
    rwa [neg_one_smul] at h1
  · exact Deg.one 0
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
