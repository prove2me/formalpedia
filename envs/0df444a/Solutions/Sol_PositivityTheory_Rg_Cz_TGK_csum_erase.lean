-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.csum_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:43.169177+00:00
-- url     : https://prove2.me/submissions/5783b786-1c99-4bb5-81be-9af00a97aab5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_cprod_erase
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
theorem _root_.solution (I : P → Fin n) (p : P) (φ : (P → Fin n) → ℂ) :
    ∑ J, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * φ J =
      ∑ b, φ (Function.update I p b) := by
  simp_rw [cprod_erase]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp
end PositivityTheory.Rg.Cz.TGK
