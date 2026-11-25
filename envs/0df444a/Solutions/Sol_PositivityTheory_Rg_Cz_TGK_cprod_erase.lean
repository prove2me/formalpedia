-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.cprod_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:14.724641+00:00
-- url     : https://prove2.me/submissions/afe0f477-c12a-4dc5-8d12-464edbe9808b

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
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution (I J : P → Fin n) (p : P) (x : ℂ) :
    (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * x =
      ∑ b, if J = Function.update I p b then x else 0 := by
  by_cases h : ∀ q, q ≠ p → I q = J q
  · rw [Finset.prod_eq_one, one_mul, Finset.sum_eq_single (J p)]
    · rw [if_pos]; funext q; by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, h q hq]
    · intro b _ hb; rw [if_neg]; intro hJ; apply hb; rw [hJ]; simp
    · simp
    · intro q hq; rw [h q (Finset.ne_of_mem_erase hq)]; simp
  · push Not at h
    obtain ⟨q, hqp, hq⟩ := h
    have h0 : ∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩) (Matrix.one_apply_ne hq)
    rw [h0, zero_mul]
    refine (Finset.sum_eq_zero fun b _ => if_neg ?_).symm
    intro hJ; apply hq; rw [hJ, Function.update_of_ne hqp]
end PositivityTheory.Rg.Cz.TGK
