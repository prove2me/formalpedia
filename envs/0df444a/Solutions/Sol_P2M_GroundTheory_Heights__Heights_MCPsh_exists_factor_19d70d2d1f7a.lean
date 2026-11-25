-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_exists_factor_19d70d2d1f7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:15.048563+00:00
-- url     : https://prove2.me/submissions/482210ce-7fa5-4cc5-b6e1-be925965dc29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {A : Matrix κ κ ℂ} (hA : A.PosDef) :
    ∃ B : Matrix κ κ ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, hB⟩
  have hdet : A.det ≠ 0 := (hA.det_pos).ne'
  rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose] at hdet
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
end GroundTheory.Heights₂.Heights.MCPsh
