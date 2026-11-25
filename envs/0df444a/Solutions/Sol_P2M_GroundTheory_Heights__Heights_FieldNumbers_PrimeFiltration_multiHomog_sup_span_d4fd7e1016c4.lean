-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_sup_span_d4fd7e1016c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:06:56.30718+00:00
-- url     : https://prove2.me/submissions/d958184d-9947-4b26-a8f1-0544248b6872

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_lexGrading_c1dd638887ba

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) {s : MRing ι F}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (J ⊔ Ideal.span {s}) := by
  refine multiHomog_of_isHomogeneous ((isHomogeneous_of_multiHomog hJ).sup ?_)
  refine Ideal.homogeneous_span _ _ ?_
  rintro x rfl
  exact ⟨_, mem_lexGrading hs⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
