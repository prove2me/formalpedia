-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.prod_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:17.362783+00:00
-- url     : https://prove2.me/submissions/7f93a7cb-961f-4f25-9302-d292b9ffffee

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
theorem _root_.solution (I J : P → Fin n) :
    ∏ q, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)
end PositivityTheory.Rg.Cz.TGK
