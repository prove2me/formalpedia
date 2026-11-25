-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_mk_ne_zero_6609c3a01637
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:54.582837+00:00
-- url     : https://prove2.me/submissions/a757ada9-f9a1-4031-a6b4-113bf42cff29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase

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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by
  unfold blockMonomial
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro k _
  rw [map_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hi k
end GroundTheory.Heights₂.Heights.FieldNumbers
