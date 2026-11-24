-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:55.816464+00:00
-- url     : https://prove2.me/submissions/7ca77b83-a328-42a2-9ebf-ee9509831449

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (g : MvPolynomial (Fin k × Fin n) F) :
    (∀ u ∈ incidence I k, aeval u g = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl g ∈ (incidenceIdeal I k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F) (incidenceIdeal I k)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, hx, hI, hlin⟩, mul_zero]
  · rintro h u ⟨x, hx, hI, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim u x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename] at this
    simpa [hj] using this
end GroundTheory.Heights₂.Heights.ChowFormExtend
