-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.cA_rl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:37:22.156771+00:00
-- url     : https://prove2.me/submissions/96241d01-08af-4458-bf31-218c46ef282f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
import Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_rl_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_alt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_cA_apply
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution {C : Type} [DecidableEq C] (e : P ≃ Q) (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA (col ∘ e.symm) (b ∘ e.symm) (rl e f) = cA col b f := by
  simp only [cA_apply, alt_apply, rl_apply]
  symm
  refine Finset.sum_equiv (Equiv.permCongr e) (fun σ => ?_) (fun σ _ => ?_)
  · simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
    exact ⟨fun h q => h _, fun h p => by simpa using h (e p)⟩
  · rw [Equiv.Perm.sign_permCongr]
    congr 2
    funext x
    simp [Equiv.permCongr_apply]
end PositivityTheory.Rg.Cz.TrOf
