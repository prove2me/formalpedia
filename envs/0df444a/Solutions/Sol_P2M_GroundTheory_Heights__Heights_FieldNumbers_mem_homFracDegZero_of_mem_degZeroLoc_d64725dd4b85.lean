-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:13:00.735826+00:00
-- url     : https://prove2.me/submissions/aebca6b2-859d-43de-bcbc-a90dae773589

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank

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
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by
  intro x hx
  refine (Algebra.adjoin_le (S := (homFracDegZero P).toSubalgebra) ?_) hx
  rintro _ ⟨b, f, g, hf, hg, hgP, -, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgP, rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
