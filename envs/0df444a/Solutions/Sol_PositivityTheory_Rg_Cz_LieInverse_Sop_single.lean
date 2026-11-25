-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.LieInverse.Sop_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:04.32745+00:00
-- url     : https://prove2.me/submissions/57b80f5f-9498-4fdd-a1d8-0935f753d882

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
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
open PositivityTheory.Rg.Cz.LieInverse
namespace PositivityTheory.Rg.Cz.LieInverse
theorem _root_.solution {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by
  unfold Sop
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro b _ hb; simp [Matrix.single_apply, hb, Ne.symm hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]
  · simp
end PositivityTheory.Rg.Cz.LieInverse
