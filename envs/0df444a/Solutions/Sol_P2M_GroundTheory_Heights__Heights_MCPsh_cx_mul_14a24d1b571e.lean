-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_cx_mul_14a24d1b571e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:12.606802+00:00
-- url     : https://prove2.me/submissions/168fd569-67ee-47b4-8a9e-1752cb5cab09

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
theorem _root_.solution (Y Z : Matrix ι ι ℝ) : cx (Y * Z) = cx Y * cx Z :=
  Matrix.map_mul (f := Complex.ofRealHom)
end GroundTheory.Heights₂.Heights.MCPsh
