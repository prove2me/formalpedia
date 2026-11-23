-- Prove2me | solution 1 for P2M_GlobalTheory_factorPow_eval__9207485a8623
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:03.253566+00:00
-- url     : https://prove2.me/submissions/3b0afb18-f973-4bba-bae8-56d3cf54a609

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution (J : Ideal A) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  induction x using AdicCompletion.induction_on with
  | _ x =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    have := (x.property h).symm
    rw [SModEq.sub_mem] at this
    simpa using this
end GlobalTheory
