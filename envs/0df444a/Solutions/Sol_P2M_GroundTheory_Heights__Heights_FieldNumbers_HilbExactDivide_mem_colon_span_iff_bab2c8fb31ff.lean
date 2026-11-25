-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_mem_colon_span_iff_bab2c8fb31ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:07.811569+00:00
-- url     : https://prove2.me/submissions/d9a82153-88a4-4d99-a230-2e7ff4093e4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide

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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
theorem _root_.solution {I : Ideal (MRing ι F)} {s g : MRing ι F} :
    g ∈ I.colon (Ideal.span {s}) ↔ g * s ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    simpa [smul_eq_mul] using h s (Ideal.subset_span rfl)
  · intro h x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [smul_eq_mul, show g * (t * s) = t * (g * s) by ring]
    exact I.mul_mem_left t h
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
