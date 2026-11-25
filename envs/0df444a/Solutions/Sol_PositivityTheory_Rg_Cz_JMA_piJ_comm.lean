-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.piJ_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:59.480056+00:00
-- url     : https://prove2.me/submissions/65ffcc22-9e7d-4a20-b748-a7c171609d5a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_piJ_comm_adj
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) (m : ℕ) (u : ℂ)
    (σ : Equiv.Perm (Fin m)) : Commute (PiJ m E u) (pm σ) := by
  cases m with
  | zero =>
    rw [Subsingleton.elim σ 1, pm_one]
    exact Commute.one_right _
  | succ m =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact piJ_comm_adj hT hE u i
    | one =>
      rw [pm_one]
      exact Commute.one_right _
    | mul x y _ _ hx hy =>
      rw [pm_mul]
      exact hx.mul_right hy
end PositivityTheory.Rg.Cz.JMA
