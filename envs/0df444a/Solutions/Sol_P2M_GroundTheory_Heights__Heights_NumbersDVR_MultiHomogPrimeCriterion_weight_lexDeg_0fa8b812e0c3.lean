-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:35.385414+00:00
-- url     : https://prove2.me/submissions/9f1cb069-1d85-4ade-93df-82e8aa7d8327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion

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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]
end GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
