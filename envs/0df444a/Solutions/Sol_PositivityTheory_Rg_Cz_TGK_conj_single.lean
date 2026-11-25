-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.conj_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:10.652918+00:00
-- url     : https://prove2.me/submissions/1c271dd0-83a7-4491-a3dd-92a48965b678

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ∑ c, ∑ d, (U c a * star (U d b)) • Matrix.single c d (1 : ℂ) = U * Matrix.single a b 1 * Uᴴ := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
end PositivityTheory.Rg.Cz.TGK
