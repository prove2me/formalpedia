-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:49.500703+00:00
-- url     : https://prove2.me/submissions/7fde879a-0805-4378-8117-017d05220f7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MCCusp
theorem _root_.solution {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (i : ι) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, ε * x i ^ 2 ≤ qf Z x) : Z⁻¹ i i ≤ 1 / ε := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hwi : w i = Z⁻¹ i i := by rw [hw, mulVec_single]; simp
  have h2 : qf Z w = Z⁻¹ i i := by rw [qf, hZw, dotProduct_single, mul_one, hwi]
  have hpos : 0 < Z⁻¹ i i := hZ.inv.diag_pos
  have := h w
  rw [h2, hwi] at this
  rw [le_div_iff₀ hε]
  nlinarith
end GroundTheory.Heights₂.Heights.MCCusp
