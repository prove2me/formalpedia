-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:27.220893+00:00
-- url     : https://prove2.me/submissions/5de0417b-87bf-4961-8108-de4e5708c721

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint

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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (i : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) i e) e := by
  have h : IsWeightedHomogeneous (blockWeight ι) (chartMonomial (F := F) i e)
      (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ =>
      (isWeightedHomogeneous_X (R := F) (blockWeight ι) ⟨k, i k⟩).pow (e k)
  have he : (∑ k ∈ Finset.univ, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
