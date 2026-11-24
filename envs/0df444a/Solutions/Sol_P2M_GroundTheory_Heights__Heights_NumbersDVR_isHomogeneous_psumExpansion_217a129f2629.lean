-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:39.383065+00:00
-- url     : https://prove2.me/submissions/da192d93-83f5-4723-80cf-52242623d250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (N k : ℕ) (i : Fin N) :
    (psumExpansion N k i).IsHomogeneous (k - 1) := by
  unfold psumExpansion
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j + (k - 1 - j) = k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have h := ((isHomogeneous_X ℤ (Sum.inl i : Fin N ⊕ Fin N)).pow j).mul
    ((isHomogeneous_X ℤ (Sum.inr i : Fin N ⊕ Fin N)).pow (k - 1 - j))
  simpa [hj'] using h
end GroundTheory.Heights₂.Heights.NumbersDVR
