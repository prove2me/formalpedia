-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_inv_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:59.234266+00:00
-- url     : https://prove2.me/submissions/7d41811e-a3ef-41e4-b0d5-3e98b3f64cfd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_const
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_inv_entry_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {M : E n → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b))
    (hd : ∀ y, (M y).det ≠ 0) (w : Fin n → Fin n → ℂ) (y : E n) (N : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, dirC (fun y => M y a b) w y = N a b) (a b : Fin n) :
    dirC (fun y => (M y)⁻¹ a b) w y = (-((M y)⁻¹ * N * (M y)⁻¹)) a b := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c d => dirC (fun y => (M y)⁻¹ c d) w y
  have hI := contDiff_inv_entry_of hM hd
  have key : M y * D = -(N * (M y)⁻¹) := by
    refine Matrix.ext fun c d => ?_
    have e : (fun x => ∑ j, M x c j * (M x)⁻¹ j d) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
      funext x; rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hd x))]
    have h2 := congrArg (fun f => dirC f w y) e
    rw [dirC_const, dirC_sum _ (fun j => diffAt_of ((hM c j).mul (hI j d)) y)] at h2
    simp only [fun j => dirC_mul (diffAt_of (hM c j) y) (diffAt_of (hI j d) y) w, hN] at h2
    rw [Finset.sum_add_distrib] at h2
    rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.mul_apply]
    simp only [D, Matrix.of_apply]
    rw [eq_neg_iff_add_eq_zero, ← h2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hu := isUnit_iff_ne_zero.mpr (hd y)
  have e2 : D = (M y)⁻¹ * (M y * D) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have e3 : dirC (fun y => (M y)⁻¹ a b) w y = D a b := rfl
  rw [e3, e2, key, Matrix.mul_neg, Matrix.mul_assoc]
end PositivityTheory.Rg.Sw.WR.B
