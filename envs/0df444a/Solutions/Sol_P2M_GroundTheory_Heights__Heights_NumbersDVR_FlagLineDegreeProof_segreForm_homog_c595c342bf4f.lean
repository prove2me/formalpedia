-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_segreForm_homog_c595c342bf4f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:45.615062+00:00
-- url     : https://prove2.me/submissions/35a8f531-bab0-4bf6-a2ba-b17299d5efef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
theorem _root_.solution {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι R)) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι R))
    (fun k => Pi.single k 1) (w := blockWeight ι) (fun k _ => isWeightedHomogeneous_X R _ _)
  rwa [Finset.univ_sum_single (fun _ : K => (1 : ℕ))] at h
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
