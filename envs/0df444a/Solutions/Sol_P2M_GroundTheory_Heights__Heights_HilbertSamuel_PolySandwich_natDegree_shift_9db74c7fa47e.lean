-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:59.262883+00:00
-- url     : https://prove2.me/submissions/56673f8b-6ed8-4c3b-98a1-8486e945172a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial Filter
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PolySandwich
theorem _root_.solution (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]
end PolySandwich
end GroundTheory.Heights₂.Heights.HilbertSamuel
