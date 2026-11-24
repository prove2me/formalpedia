-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_mulVec_injective_of_rank_78b168dcc192
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:36.282958+00:00
-- url     : https://prove2.me/submissions/492fdda7-8379-459e-8f29-af8e4fee089c

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
theorem _root_.solution {F : Matrix ι κ ℂ} (h : F.rank = Fintype.card κ) :
    Function.Injective F.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
  rw [← Matrix.rank, h, Module.finrank_fintype_fun_eq_card] at hrn
  have hk : LinearMap.ker F.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp hk
end GroundTheory.Heights₂.Heights.MCPsh
