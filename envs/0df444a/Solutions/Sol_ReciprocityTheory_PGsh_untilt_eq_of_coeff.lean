-- Prove2me | solution 1 for ReciprocityTheory.PGsh.untilt_eq_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:38.742944+00:00
-- url     : https://prove2.me/submissions/60930f80-23c8-41cf-a311-ea47b1c6cbdd

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Ideal
namespace ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
section Untilt
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
private lemma pow_p_pow_eq (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    f n ^ p ^ n = f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hf, ih]
end Untilt
section Roots
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
end Roots
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (x : PreTilt O p) (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n)
    (hx : ∀ n, Perfection.coeff (ModP O p) p n x = Ideal.Quotient.mk (span {(p : O)}) (f n)) :
    x.untilt = f 0 := by
  show Perfection.teichmuller p (span {(p : O)}) x = f 0
  exact Perfection.teichmuller_spec fun n => ⟨f n, (hx n).symm, by rw [pow_p_pow_eq f hf n]⟩
end ReciprocityTheory.PGsh
