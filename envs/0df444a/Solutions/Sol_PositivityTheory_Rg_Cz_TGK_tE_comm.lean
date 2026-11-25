-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.tE_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:45.372737+00:00
-- url     : https://prove2.me/submissions/8bb44aec-1004-4d1a-826c-1891cce9594c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_eAt_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_comm_eAt
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
theorem _root_.solution {ι : Type} [DecidableEq ι] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (hcomm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) (lab : P → ι) (τ τ' : ι) (h : τ ≠ τ')
    (a b c d : Fin n) : Commute (tE (fib lab τ) (E τ) a b) (tE (fib lab τ') (E τ') c d) := by
  unfold tE
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
  · exact (hcomm τ τ' h a b c d).map (liftA n M P)
  · exact Commute.sum_right _ _ _ fun p _ => lift_comm_eAt _ _ _ _
  · exact Commute.sum_left _ _ _ fun p _ => (lift_comm_eAt _ _ _ _).symm
  · refine Commute.sum_left _ _ _ fun p hp => Commute.sum_right _ _ _ fun q hq => eAt_comm p q ?_ _ _ _ _
    rintro rfl
    simp only [fib, Finset.mem_filter] at hp hq
    exact h (hp.2.symm.trans hq.2)
end PositivityTheory.Rg.Cz.TGK
