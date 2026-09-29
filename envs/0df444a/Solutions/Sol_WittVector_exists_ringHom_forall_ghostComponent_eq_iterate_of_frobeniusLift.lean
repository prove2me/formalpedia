-- Prove2me | solution 1 for WittVector.exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/936a949a-e2d7-5cda-989f-5f36f567e3c8

import Mathlib
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift

set_option autoImplicit false

universe u

namespace DworkSectionAux

variable {R : Type u} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

theorem ghostComponent_eq_of_coeff_eq (n : ℕ) (x y : WittVector p R)
    (h : ∀ i ≤ n, x.coeff i = y.coeff i) :
    WittVector.ghostComponent n x = WittVector.ghostComponent n y := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem eq_of_forall_ghostComponent_eq (hpnz : (p : R) ∈ nonZeroDivisors R) (x y : WittVector p R)
    (h : ∀ k, WittVector.ghostComponent k x = WittVector.ghostComponent k y) : x = y := by
  ext k
  exact WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) x y
    (fun i _ => h i) k (Nat.lt_succ_self k)

theorem exists_forall_ghostComponent_eq (hpnz : (p : R) ∈ nonZeroDivisors R) (σ : R →+* R)
    (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)}) (g : ℕ → R)
    (hg : ∀ k : ℕ, g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
    ∃ x : WittVector p R, ∀ k, WittVector.ghostComponent k x = g k := by
  have hex : ∀ n : ℕ, ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k :=
    fun n => WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem p σ hσ n g
      (fun k _ => hg k)
  choose xs hxs using hex
  refine ⟨WittVector.mk p fun k => (xs (k + 1)).coeff k, fun k => ?_⟩
  have hcoeff : ∀ n k, k < n → (WittVector.mk p fun k => (xs (k + 1)).coeff k).coeff k
      = (xs n).coeff k := by
    intro n k hk
    have h1 := WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) (xs (k + 1))
      (xs n) (fun i hi => by rw [hxs (k + 1) i hi, hxs n i (by omega)]) k (Nat.lt_succ_self k)
    rw [← h1, WittVector.coeff_mk]
  rw [ghostComponent_eq_of_coeff_eq p k _ (xs (k + 1))
    (fun i hi => hcoeff (k + 1) i (Nat.lt_succ_of_le hi)), hxs (k + 1) k (Nat.lt_succ_self k)]

end DworkSectionAux

open DworkSectionAux in
theorem solution
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (σ : R →+* R) (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)}) :
    ∃ s : R →+* WittVector p R, ∀ (a : R) (n : ℕ),
      WittVector.ghostComponent n (s a) = (⇑σ)^[n] a := by
  have hex : ∀ a : R, ∃ x : WittVector p R, ∀ k, WittVector.ghostComponent k x = (⇑σ)^[k] a := by
    intro a
    refine exists_forall_ghostComponent_eq p hp σ hσ (fun k => (⇑σ)^[k] a) (fun k => ?_)
    show (⇑σ)^[k + 1] a - σ ((⇑σ)^[k] a) ∈ _
    rw [Function.iterate_succ_apply', sub_self]
    exact Ideal.zero_mem _
  choose s hs using hex
  have hiter : ∀ n : ℕ, (⇑σ)^[n] = ⇑(σ ^ n) := fun n => (RingHom.coe_pow σ n).symm
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hs⟩
  · apply eq_of_forall_ghostComponent_eq p hp
    intro k; rw [hs, hiter, map_one, map_one]
  · intro a b
    apply eq_of_forall_ghostComponent_eq p hp
    intro k; rw [hs, map_mul, hs, hs, hiter, map_mul]
  · apply eq_of_forall_ghostComponent_eq p hp
    intro k; rw [hs, hiter, map_zero, map_zero]
  · intro a b
    apply eq_of_forall_ghostComponent_eq p hp
    intro k; rw [hs, map_add, hs, hs, hiter, map_add]

end S_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift
end P2MW
export P2MW.S_WittVector_exists_ringHom_forall_ghostComponent_eq_iterate_of_frobeniusLift (solution)
