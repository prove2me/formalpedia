-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_chowForm_vanish_aa54c6828c1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:26.603751+00:00
-- url     : https://prove2.me/submissions/06bf61d7-5880-48c4-81de-ffa158034d80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_eval_pairing_f70de561052b

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution {W : Ideal (MvPolynomial (Fin n) ℂ)} {g : MvPolynomial (Fin 1 × Fin n) ℂ}
    (hg : IsChowForm W 1 g) {y : Fin n → ℂ} (hy0 : y ≠ 0) (hy : ∀ q ∈ W, eval y q = 0)
    (u : Fin 1 × Fin n → ℂ) (hu : eval u (pairing y) = 0) : eval u g = 0 := by
  set φ := algebraMap ℂ (AlgebraicClosure ℂ) with hφ
  have hu' : ∑ j, u (0, j) * y j = 0 := by
    rw [eval_pairing] at hu
    simpa [mul_comm] using hu
  have hinc : (φ ∘ u) ∈ incidence W 1 := by
    refine ⟨φ ∘ y, ?_, ?_, ?_⟩
    · intro h
      apply hy0
      funext j
      have := congrFun h j
      simpa using this
    · intro q hq
      rw [aeval_algebraMap_apply]
      simp [hy q hq]
    · intro i
      obtain rfl := Subsingleton.elim i 0
      simp only [Function.comp_apply, ← map_mul, ← map_sum, hu', map_zero]
  have h := (hg.2 g).mpr dvd_rfl _ hinc
  rw [aeval_algebraMap_apply] at h
  simpa using h
end GroundTheory.Heights₂.Heights.PointLine
