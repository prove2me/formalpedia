-- Prove2me | solution 1 for PI.UD.gramStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:52.283878+00:00
-- url     : https://prove2.me/submissions/836c41d7-7da5-4ffc-b925-2083ba8fdd0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Decomp
import Theorems.Thm_PI_UD_herm_decomp
import Theorems.Thm_PI_UD_det_ne_zero_of_unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexOrder
namespace PI.UD
private theorem exists_diagonal_unitary_gram_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) :
    ∃ (s : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), (∀ i, s i ≠ 0) ∧ Vᴴ * V = 1 ∧
      V * Vᴴ = 1 ∧ G = (diagonal s * Vᴴ)ᴴ * (diagonal s * Vᴴ) := by
  obtain ⟨V, h1, h2, hV⟩ := herm_decomp hG.1
  refine ⟨fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ), V, ?_, h1, h2, ?_⟩
  · intro i
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hG.eigenvalues_pos i)).ne'
  · have hd : (diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
        diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)) =
        diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc G = V * diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) * Vᴴ := hV
      _ = V * ((diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
          diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ))) * Vᴴ := by rw [hd]
      _ = _ := by simp only [Matrix.mul_assoc]
end PI.UD
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution : GramStep := by
  intro n G hG
  obtain ⟨s, V, hs, hV1, -, hGe⟩ := exists_diagonal_unitary_gram_of_posDef hG
  refine ⟨diagonal s * Vᴴ, hGe.symm, ?_⟩
  rw [det_mul, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
    (det_ne_zero_of_unitary hV1)
end PI.UD
