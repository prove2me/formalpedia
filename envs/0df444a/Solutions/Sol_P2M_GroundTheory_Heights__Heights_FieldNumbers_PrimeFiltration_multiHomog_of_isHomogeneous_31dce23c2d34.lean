-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_of_isHomogeneous_31dce23c2d34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:48.500003+00:00
-- url     : https://prove2.me/submissions/d402a503-b6cc-46be-8d4e-cd1cf91fd092

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12

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
theorem _root_.solution {I : Ideal (MRing ι F)}
    (h : I.IsHomogeneous (lexGrading ι F)) : IsMultiHomogIdeal I := by
  classical
  intro f hf b
  rw [← component_lex]
  exact weightedHomogeneousComponent_mem_of_mem (h := h) (hp := hf) (m := lexEmb K b)
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
