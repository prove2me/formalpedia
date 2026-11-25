-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:36.900701+00:00
-- url     : https://prove2.me/submissions/76802ec0-3c39-41ba-8564-1715c73d1572

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}
variable {z : (Σ _ : Unit, Fin 2) → ℂ}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (S : Matrix (Fin 2) (Fin 2) ℂ) (h10 : S 1 0 = 0) (h00 : S 0 0 ≠ 0) :
    quotNormSq (show 1 ≤ 2 by decide) (Sᴴ * S) = ‖S 1 1‖ ^ 2 := by
  unfold quotNormSq
  have hdet : (Sᴴ * S).det = ((‖S 0 0 * S 1 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fin_two, h10, mul_zero, sub_zero]
    rw [show star (S 0 0 * S 1 1) = (starRingEnd ℂ) (S 0 0 * S 1 1) from rfl, Complex.conj_mul']
    push_cast
    ring
  have hsub : ((Sᴴ * S).submatrix (headIdx (show 1 ≤ 2 by decide)) (headIdx (show 1 ≤ 2 by decide))).det =
      ((‖S 0 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_unique]
    have h0 : headIdx (show 1 ≤ 2 by decide) (default : Fin 1) = 0 := rfl
    simp only [Matrix.submatrix_apply, h0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h10,
      star_zero, zero_mul, add_zero]
    rw [show star (S 0 0) = (starRingEnd ℂ) (S 0 0) from rfl, Complex.conj_mul']
    push_cast
    ring
  rw [hdet, hsub, Complex.ofReal_re, Complex.ofReal_re, norm_mul, mul_pow]
  have : ‖S 0 0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h00)
  field_simp
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
