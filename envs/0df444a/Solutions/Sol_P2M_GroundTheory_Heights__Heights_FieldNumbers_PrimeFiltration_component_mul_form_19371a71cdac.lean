-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_mul_form_19371a71cdac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:15.884375+00:00
-- url     : https://prove2.me/submissions/08e6e66d-caef-40aa-82cf-a4f27843fc88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration

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
theorem _root_.solution {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (b + c) (t * s) =
      weightedHomogeneousComponent (blockWeight ι) b t * s := by
  have hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (i := b) (a := t) hs'
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact this
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
