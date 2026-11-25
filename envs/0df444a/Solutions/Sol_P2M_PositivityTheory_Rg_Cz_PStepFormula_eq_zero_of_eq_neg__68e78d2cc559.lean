-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:10.419947+00:00
-- url     : https://prove2.me/submissions/08360af6-a489-44d7-93bb-2f0b25e6e8af

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA

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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {X : Type} [AddCommGroup X] [Module ℂ X] {x : X} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
end PositivityTheory.Rg.Cz.PStepFormula
