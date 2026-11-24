-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_proof_14040d77a0cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:45.380578+00:00
-- url     : https://prove2.me/submissions/77109c76-8777-4d67-aa52-a753ded0bdca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0

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
open GroundTheory.Heights₂.Heights.ChowFormExtend
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (h : RadicalBaseChange.Statement) : ChowFormExtend.Statement := by
  intro K L _ _ _ σ n k I f hf
  let _ : Algebra K L := σ.toAlgebra
  exact isChowForm_map h I f hf
end GroundTheory.Heights₂.Heights.ChowFormExtend
