-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_GradedFinite_proof_4a0254b94345
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:26.948168+00:00
-- url     : https://prove2.me/submissions/d9324a61-5faf-417c-8ccc-1e5fd6c2b39d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finiteDimensional_multiHomogForms_38c8ede14e27

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace GradedFinite
theorem _root_.solution : GradedFinite.Statement := by
  intro F _ K _ _ ι _ I m
  have hfin := finiteDimensional_multiHomogForms (ι := ι) F m
  have hP : FiniteDimensional F (gradedPiece I m) := by
    unfold gradedPiece
    exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)
  refine ⟨hP, ?_⟩
  unfold hilbFn
  rw [if_pos fun k => Int.natCast_nonneg (m k)]
  simp only [Int.toNat_natCast]
end GradedFinite
end GroundTheory.Heights₂.Heights.FieldNumbers
