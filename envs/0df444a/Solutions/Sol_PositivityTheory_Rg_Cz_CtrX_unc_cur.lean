-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.unc_cur
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:03.253805+00:00
-- url     : https://prove2.me/submissions/4bead003-90f9-4718-94e2-64bb11513cbc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {A B : Type} (g : TV n M (A ⊕ B)) : unc (cur g) = g := by
  funext I
  simp only [unc, cur, Sum.elim_comp_inl_inr]
end PositivityTheory.Rg.Cz.CtrX
