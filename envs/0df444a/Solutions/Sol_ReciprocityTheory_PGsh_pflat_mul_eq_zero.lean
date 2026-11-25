-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pflat_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:34.177732+00:00
-- url     : https://prove2.me/submissions/272327e9-b5aa-4a3c-b7ce-4960adc9357b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open WittVector Ideal TensorProduct
namespace ReciprocityTheory.PGsh
section Witt
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]
private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih
end Witt
section Tilt
variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Tilt
section Main
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end Main
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)
end ReciprocityTheory.PGsh
