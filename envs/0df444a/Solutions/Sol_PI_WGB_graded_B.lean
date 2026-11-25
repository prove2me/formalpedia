-- Prove2me | solution 1 for PI.WGB.graded_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:05.418051+00:00
-- url     : https://prove2.me/submissions/88b2f46e-7cd6-4077-b94e-366fa5ae5024

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Theorems.Thm_PI_WGB_rowAct_diag_homog
import Theorems.Thm_PI_WGB_comp_sum_B
import Theorems.Thm_PI_WGB_comp_zero_B
import Theorems.Thm_PI_WGB_sep_mem_B
import Theorems.Thm_PI_WGB_torus_mem_B
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) (m : Fin n → ℕ) :
    weightedHomogeneousComponent (wnB n N) m f ∈ W := by
  classical
  let F := f.support.image (Finsupp.weight (wnB n N))
  by_cases hm : m ∈ F
  · refine sep_mem_B (T := Fin n → ℂˣ)
      (fun t => (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N fun j => (t j : ℂ)))).toLinearMap)
      (fun m t => chiB (fun j => (t j : ℂ)) m) W (fun t x hx => torus_mem_B h lam W hW t x hx) ?_ F
      (fun m => weightedHomogeneousComponent (wnB n N) m f) ?_ ?_ m hm
    · intro i j hij
      obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
      let τ : Fin n → ℂˣ := fun l => if l = k then Units.mk0 (2 : ℂ) two_ne_zero else 1
      have key : ∀ a : Fin n → ℕ, chiB (fun l => ((τ l : ℂˣ) : ℂ)) a = (2 : ℂ) ^ a k := by
        intro a
        unfold chiB
        rw [Finset.prod_eq_single k]
        · simp [τ]
        · intro l _ hl
          simp [τ, hl]
        · simp
      refine ⟨τ, ?_⟩
      show chiB (fun l => ((τ l : ℂˣ) : ℂ)) i ≠ chiB (fun l => ((τ l : ℂˣ) : ℂ)) j
      rw [key, key]
      intro he
      apply hk
      have h2 : ((2 ^ i k : ℕ) : ℂ) = ((2 ^ j k : ℕ) : ℂ) := by push_cast; exact he
      exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)
    · intro i _ t
      exact rowAct_diag_homog _ _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [comp_sum_B]
      · exact hf
      · intro e he
        exact Finset.mem_image_of_mem _ he
  · rw [comp_zero_B]
    · exact W.zero_mem
    · intro e he hw
      exact hm (hw ▸ Finset.mem_image_of_mem _ he)
end PI.WGB
