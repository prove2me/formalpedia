-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:40.744271+00:00
-- url     : https://prove2.me/submissions/8973d169-787b-4a22-b82d-70975a88d150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    degZeroLoc P 𝒲₂ ≤ degZeroLoc P 𝒲₁ := by
  unfold degZeroLoc
  apply Algebra.adjoin_mono
  rintro _ ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
  exact ⟨b, f, g, hf, hg, hgP, fun W hW => hgW W (h𝒲 hW), rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
