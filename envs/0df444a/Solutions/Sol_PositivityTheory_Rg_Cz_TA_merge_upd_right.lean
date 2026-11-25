-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.merge_upd_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:39.540808+00:00
-- url     : https://prove2.me/submissions/7339db8d-d8d7-4330-996e-8689e7312518

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
omit [Fintype P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · have hp : p ≠ x.1 := fun e => x.2 (e ▸ h)
    simp [merge, h, hp]
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // ¬ q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]
end PositivityTheory.Rg.Cz.TA
