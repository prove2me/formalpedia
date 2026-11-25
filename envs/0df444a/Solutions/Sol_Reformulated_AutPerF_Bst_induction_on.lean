-- Prove2me | solution 1 for Reformulated.AutPerF.Bst.induction_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:33.065941+00:00
-- url     : https://prove2.me/submissions/b97c33ba-065b-4edb-b99e-f1a87cb4b4a2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.Bst
namespace Reformulated.AutPerF.Bst
theorem _root_.solution {P : Bst p R → Prop} (x : Bst p R)
    (h₁ : ∀ a : Bcris p R, P (algebraMap _ _ a)) (h₂ : ∀ x y, P x → P y → P (x + y))
    (h₃ : ∀ x ϖ, P x → P (x * logFlat ϖ)) : P x := by
  obtain ⟨f, rfl⟩ := mk_surjective p R x
  induction f using MvPolynomial.induction_on with
  | C a => have := h₁ a; rwa [← (mk p R).commutes] at this
  | add f g hf hg => rw [map_add]; exact h₂ _ _ hf hg
  | mul_X f ϖ hf => rw [map_mul]; exact h₃ _ ϖ hf
end Reformulated.AutPerF.Bst
