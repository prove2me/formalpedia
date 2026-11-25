-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.cpart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:13.429941+00:00
-- url     : https://prove2.me/submissions/85f17858-1e45-40e8-b46c-87b17318d06c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
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
omit [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution {ι : Type} [DecidableEq ι] (lab : P → ι) (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ)
    (I : P → Fin n) (h : Fin n → P → ℂ) :
    ∑ p, ∑ b, cD bar τ X (lab p) (I p) b * h b p =
      ∑ p ∈ fib lab τ, ∑ b, X (I p) b * h b p + ∑ p ∈ fib lab (bar τ), ∑ b, star (X (I p) b) * h b p := by
  unfold fib
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold cD
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]
end PositivityTheory.Rg.Cz.TGK
