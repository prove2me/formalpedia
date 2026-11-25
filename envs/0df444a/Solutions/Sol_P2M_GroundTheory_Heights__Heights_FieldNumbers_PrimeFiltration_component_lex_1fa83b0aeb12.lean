-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:10:45.829824+00:00
-- url     : https://prove2.me/submissions/1bb0a80e-ebcb-4f16-aacb-257971382ced

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_lexEmb_injective_2e035ab13206
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_weight_lexWeight_8cd877a192d7

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
open Classical
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (f : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) (lexEmb K b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexWeight, lexEmb_injective.eq_iff]
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
