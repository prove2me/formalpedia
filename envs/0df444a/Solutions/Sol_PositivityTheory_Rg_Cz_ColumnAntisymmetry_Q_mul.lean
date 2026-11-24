-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:20.035386+00:00
-- url     : https://prove2.me/submissions/1ce24554-ee62-4c79-83f5-be86785ab5ce

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul


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
theorem _root_.solution (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {σ τ : Equiv.Perm (Fin m)} (h1 : Q L σ) (h2 : Q L τ) :
    Q L (σ * τ) := by
  unfold Q at *
  rw [pm_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.smul_comp, h2, smul_smul,
    Equiv.Perm.sign_mul]
  push_cast
  ring_nf
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
