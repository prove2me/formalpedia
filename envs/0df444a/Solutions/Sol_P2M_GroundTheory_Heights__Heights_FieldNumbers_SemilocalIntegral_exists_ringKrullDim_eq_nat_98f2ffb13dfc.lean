-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:25:13.375956+00:00
-- url     : https://prove2.me/submissions/b090a567-22e1-4daf-bb0a-165a31ead1eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_lt_top
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3


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
open GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
theorem _root_.solution (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := ringKrullDim_nonneg_of_nontrivial
  have h2 := PFContracted.ringKrullDim_lt_top (F := F) Q
  cases h : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [h] at h1
    exact absurd h1 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [h] at h2
      exact absurd h2 (by simp)
    | coe D => exact ⟨D, rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
