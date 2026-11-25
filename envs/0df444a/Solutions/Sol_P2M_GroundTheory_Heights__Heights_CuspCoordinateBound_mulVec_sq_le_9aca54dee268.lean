-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_mulVec_sq_le_9aca54dee268
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:06.138801+00:00
-- url     : https://prove2.me/submissions/de5a2818-6dce-4c9c-8766-380647ecd9a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCoordinateBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspCoordinateBound
namespace GroundTheory.Heights₂.Heights.CuspCoordinateBound
theorem _root_.solution {g : ℕ} (X : Matrix (Fin g) (Fin g) ℝ) (M : ℝ) (k : Fin g)
    (hX : ∀ l, |X k l| ≤ M) (β : Fin g → ℝ) :
    (X *ᵥ β) k ^ 2 ≤ g * M ^ 2 * ∑ l, β l ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => X k l) β
  have hrow : ∑ l, X k l ^ 2 ≤ g * M ^ 2 := by
    calc ∑ l, X k l ^ 2 ≤ ∑ _l : Fin g, M ^ 2 := Finset.sum_le_sum fun l _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hX l) 2
      _ = g * M ^ 2 := by simp
  have hb : 0 ≤ ∑ l, β l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have he : (X *ᵥ β) k = ∑ l, X k l * β l := rfl
  rw [he]
  calc _ ≤ (∑ l, X k l ^ 2) * ∑ l, β l ^ 2 := hcs
    _ ≤ g * M ^ 2 * ∑ l, β l ^ 2 := mul_le_mul_of_nonneg_right hrow hb
end GroundTheory.Heights₂.Heights.CuspCoordinateBound
