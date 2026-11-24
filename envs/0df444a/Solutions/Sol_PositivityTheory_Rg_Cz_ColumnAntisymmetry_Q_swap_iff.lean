-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_swap_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:47.983901+00:00
-- url     : https://prove2.me/submissions/8c5c893e-286c-4707-b6e7-5334c8406475

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {p q : Fin m} (h : p ≠ q) :
    Q L (Equiv.swap p q) ↔ L ∘ₗ pm (Equiv.swap p q) = -L := by
  unfold Q
  rw [Equiv.Perm.sign_swap h]
  simp
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
