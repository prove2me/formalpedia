-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.xJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:42.832071+00:00
-- url     : https://prove2.me/submissions/f7123f27-aaaa-446c-8edc-167de11fa101

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pm_swap_eq
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) :
    xJ E j = ∑ a, ∑ b, tE (Finset.univ.filter (· < j)) E a b * eAt j b a := by
  have hs : ∀ i ∈ Finset.univ.filter (· < j),
      pm (Equiv.swap i j) = ∑ a, ∑ b, (eAt i a b * eAt j b a : Module.End ℂ (TV n M (Fin m))) :=
    fun i hi => pm_swap_eq i j (ne_of_lt (Finset.mem_filter.1 hi).2)
  show Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j) = _
  rw [Finset.sum_congr rfl hs]
  simp only [tE, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
end PositivityTheory.Rg.Cz.JMA
