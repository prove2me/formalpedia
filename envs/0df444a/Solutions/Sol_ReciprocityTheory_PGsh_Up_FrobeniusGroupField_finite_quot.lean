-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:54.436567+00:00
-- url     : https://prove2.me/submissions/02bdf5c2-dc3c-4352-98d5-3cecc83be3fa

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (f : ℤ_[p][X]) (hf : f.Monic) :
    Finite (AdjoinRoot f ⧸ Ideal.span {(p : AdjoinRoot f)}) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  let b := (AdjoinRoot.powerBasis' hf).basis
  let Φ : (Fin (AdjoinRoot.powerBasis' hf).dim → ZMod p) → S ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ i, (((c i).val : ℕ) : ℤ_[p]) • b i)
  refine Finite.of_surjective Φ fun y => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => PadicInt.toZMod (b.repr s i), ?_⟩
  simp only [Φ]
  rw [Ideal.Quotient.eq]
  have key : (∑ i, (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) • b i) - s =
      ∑ i, ((((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hz := PadicInt.toZMod_spec (b.repr s i)
  rw [ZMod.cast_eq_val, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hz
  obtain ⟨w, hw⟩ := hz
  have : (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i = -(w * p) := by
    rw [hw]; ring
  rw [this, neg_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact J.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
