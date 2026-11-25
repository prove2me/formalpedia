-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.colF_lab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:09.969835+00:00
-- url     : https://prove2.me/submissions/482e10e1-c698-4b79-89c7-3bda2ad03d31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (nu : ι → Fin n → ℕ) (H : Finset ι)
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution (bar : ι → ι) (p p' : Pos nu H) (h : colF nu H p = colF nu H p') :
    lab3 bar (labQ nu) (tl H) p = lab3 bar (labQ nu) (tl H) p' := by
  rcases p with p | k | k <;> rcases p' with p' | k' | k' <;> simp [colF, lab3, colQ, Nat.pair_eq_pair] at h ⊢
  all_goals first | exact h.1 | rw [h.1] | exact (Fintype.equivFin ι).injective (Fin.ext h.1)
end PositivityTheory.Rg.Cz.KTy
