-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.det_one_add_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:25.153227+00:00
-- url     : https://prove2.me/submissions/c57665aa-5bbf-43d1-81a2-51f634c82139

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_spectral
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_conj_det
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_one_sub_conj

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (y : E n) : ∃ lam : Fin n → ℝ, ∀ c : ℂ,
    ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) ∧ ((1 : Mc n) + herm y * herm y).det = ∏ i, (1 + (lam i : ℂ) ^ 2) := by
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨lam, fun c => ⟨?_, ?_⟩⟩
  · rw [hy, one_sub_conj k hk, conj_det k hk]
    rw [show (1 : Mc n) + c • Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => 1 + c * lam i) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]]
    simp
  · have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
      rw [hy]
      calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
          = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp
end PositivityTheory.Rg.Sw.WR.K.GB
