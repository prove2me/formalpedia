-- Prove2me | solution 1 for PI.UnitaryDimensionFormula.FrameAlg.dual_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:13.236375+00:00
-- url     : https://prove2.me/submissions/eb583048-0e4e-4540-8351-f5dc54b6d3ec

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_smul_left
import Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}
namespace PI.UnitaryDimensionFormula.FrameAlg
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {k : ℕ} (b c : Fin k → n → A) (ε : A) (M : Matrix (Fin k) (Fin k) A)
    (hM : M * Matrix.of (fun l j => Formalism.UG.hform σ J (c l) (b j)) = ε • (1 : Matrix (Fin k) (Fin k) A))
    (i j : Fin k) :
    Formalism.UG.hform σ J (∑ l, σ (M i l) • c l) (b j) = if i = j then ε else 0 := by
  have h := congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [h_sum_left]
  simp only [h_smul_left, hσ]
  rw [h]
  split_ifs <;> simp
end PI.UnitaryDimensionFormula.FrameAlg
