-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_isMultiHomog_c26d37c8b0f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:49.01387+00:00
-- url     : https://prove2.me/submissions/c1c98c3e-48b6-4c73-b370-1c523f89f94b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))
  have hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hm] at h
  exact h
end GroundTheory.Heights₂.Heights.FieldNumbers
