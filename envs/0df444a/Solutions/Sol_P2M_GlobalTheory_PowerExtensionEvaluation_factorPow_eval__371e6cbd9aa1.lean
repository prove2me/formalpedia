-- Prove2me | solution 1 for P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:30.452548+00:00
-- url     : https://prove2.me/submissions/b7b5c2be-10a6-4af0-9ee3-710f71b04cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation
namespace GlobalTheory.PowerExtensionEvaluation
theorem _root_.solution {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s.val n) = Ideal.Quotient.mk (I ^ m) (s.val m)
  rw [Ideal.Quotient.eq]
  have h := s.property hle
  rw [SModEq.sub_mem] at h
  have h2 : s.val m - s.val n ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  have h3 := (I ^ m).neg_mem h2
  rwa [neg_sub] at h3
end GlobalTheory.PowerExtensionEvaluation
