-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_cx_inv_7b358c22ed20
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:15.304261+00:00
-- url     : https://prove2.me/submissions/abb693fb-4fb3-4f92-a331-0cb3f63b0211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_cx_one_40e68e603bc0

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
theorem _root_.solution {Y : Matrix ι ι ℝ} (hY : IsUnit Y.det) : (cx Y)⁻¹ = cx Y⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← cx_mul, Matrix.nonsing_inv_mul _ hY, cx_one]
end GroundTheory.Heights₂.Heights.MCPsh
