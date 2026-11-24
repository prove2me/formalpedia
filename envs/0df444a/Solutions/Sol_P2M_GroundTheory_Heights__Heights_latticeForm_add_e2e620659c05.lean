-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:37.490331+00:00
-- url     : https://prove2.me/submissions/7a933abd-3cba-4cc9-920b-db260281d050

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (u v : Fin m → K) :
    latticeForm (u + v) = latticeForm u + latticeForm v := by
  simp [latticeForm, add_mul, Finset.sum_add_distrib]
end GroundTheory.Heights₂.Heights
