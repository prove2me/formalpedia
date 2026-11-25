-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.sg_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:45.385262+00:00
-- url     : https://prove2.me/submissions/fef26e26-ba9a-4c0f-9263-d63e1933f7d7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (col : X → C) (b : X → Fin n) (hI : ColInj col b) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    sg col b (b ∘ π) = Equiv.Perm.sign π := by
  unfold sg
  rw [Finset.sum_eq_single π]
  · simp
  · intro σ hσ hne
    rw [if_neg]
    intro h
    apply hne
    ext p
    have hσ' := (mem_colG col σ).1 hσ p
    have hπ' := (mem_colG col π).1 hπ p
    exact hI _ _ (hσ'.trans hπ'.symm) (congrFun h p)
  · intro h
    exact absurd hπ h
end PositivityTheory.Rg.Cz.YoungTableau
