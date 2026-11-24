-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.CP.cay_inU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:33.857913+00:00
-- url     : https://prove2.me/submissions/5aef6b03-ff20-4309-86d5-768380d790be

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP

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
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.CP
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.CP
theorem _root_.solution {J Y : Matrix ι ι ℂ} (hY : Yᴴ * J + J * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹) = J := by
  have hY' : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have h1 : J * (1 - Y) = (1 + Y)ᴴ * J := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, hY', Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      sub_eq_add_neg]
  have h2 : J * (1 + Y) = (1 - Y)ᴴ * J := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, hY', Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      sub_neg_eq_add]
  have hc : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  have hB : (1 + Y)ᴴ * J * (1 + Y) = (1 - Y)ᴴ * J * (1 - Y) := by
    rw [← h1, Matrix.mul_assoc, hc, ← Matrix.mul_assoc, h2]
  have hA : ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  calc ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹)ᴴ * ((1 + Y)ᴴ * J * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ * J * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [hB]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
end PositivityTheory.SiegelWeilFormula.Krd.CP
