-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.card_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:44.987463+00:00
-- url     : https://prove2.me/submissions/af90e6a5-82ca-4c92-98c0-fac1efd7b922

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
omit [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (r : P → Prop) [DecidablePred r] :
    (Finset.univ.filter fun x : {p // q p} => r x.1).card = (Finset.univ.filter fun p => q p ∧ r p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype q)]
  congr 1
  ext p
  simp [and_comm]
end PositivityTheory.Rg.Cz.TA
