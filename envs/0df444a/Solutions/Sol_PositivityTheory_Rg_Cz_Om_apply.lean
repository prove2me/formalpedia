-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.Om_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:28.892967+00:00
-- url     : https://prove2.me/submissions/64905377-53ed-43e6-bcb5-a066855b9937

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by
  simp only [Om, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply, eAt_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I p)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero]
  · simp
end PositivityTheory.Rg.Cz
