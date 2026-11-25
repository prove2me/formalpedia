-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_colon_span_eq_of_isPrime_362b72cb0c33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:53:20.529411+00:00
-- url     : https://prove2.me/submissions/adbc550f-421d-41ef-bf40-0b77ca9f69fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {P : Ideal (MRing ι F)} (hP : P.IsPrime) {s : MRing ι F}
    (hs : s ∉ P) : P.colon (Ideal.span {s}) = P := by
  ext x
  rw [Ideal.mem_colon_span_singleton]
  exact ⟨fun h => (hP.mem_or_mem h).resolve_right hs, fun h => P.mul_mem_right s h⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
