-- Prove2me | solution 1 for WittVector.isWeightedHomogeneous_wittStructureInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/03319614-5343-5031-be80-ef9369b2074e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_isWeightedHomogeneous_wittStructureInt

set_option autoImplicit false

universe v

namespace WittVector
p2m_export "WittVector" "coeff map"
namespace WHomog
p2m_open "WittVector"

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

private theorem isWH_sub {σ M : Type*} [AddCommMonoid M] {w : σ → M} {φ ψ : MvPolynomial σ R} {m : M}
    (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ m) :
    IsWeightedHomogeneous w (φ - ψ) m := by
  rw [← mem_weightedHomogeneousSubmodule] at hφ hψ ⊢
  exact Submodule.sub_mem _ hφ hψ

private theorem isWH_bind₁ {σ τ : Type*} (w : τ → ℕ) (f : σ → MvPolynomial τ R) (m : ℕ)
    (hf : ∀ b, IsWeightedHomogeneous w (f b) m) (Φ : MvPolynomial σ R) (k : ℕ)
    (hΦ : Φ.IsHomogeneous k) : IsWeightedHomogeneous w (bind₁ f Φ) (k * m) := by
  classical
  rw [Φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hk : ∑ i ∈ d.support, d i = k := by
    have h := hΦ (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    simpa using h
  have h := (IsWeightedHomogeneous.prod d.support (fun i => f i ^ d i) (fun i => d i • m)
    fun i _ => (hf i).pow (d i)).C_mul (MvPolynomial.coeff d Φ)
  rw [← Finset.sum_smul, hk, smul_eq_mul] at h
  exact h

variable (p : ℕ) [hp : Fact p.Prime] {idx : Type*}

omit hp in

private theorem isWH_rename_wittPolynomial (b : idx) (n : ℕ) :
    IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2) (rename (fun i => (b, i)) (wittPolynomial p R n)) (p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
  rw [map_mul, rename_C, map_pow (rename (fun i => (b, i))), rename_X]
  have h := ((isWeightedHomogeneous_X R (fun bi : idx × ℕ => p ^ bi.2) (b, i)).pow (p ^ (n - i))).C_mul
    ((p : R) ^ i)
  rw [smul_eq_mul, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hi))] at h
  exact h

private theorem isWH_wittStructureRat (Φ : MvPolynomial idx ℚ) (k : ℕ) (hΦ : Φ.IsHomogeneous k) (n : ℕ) :
    IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2) (wittStructureRat p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [wittStructureRat_rec]
  refine (isWH_sub ?_ ?_).C_mul _
  · exact isWH_bind₁ _ _ (p ^ n) (fun b => isWH_rename_wittPolynomial (R := ℚ) p b n) Φ k hΦ
  · refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i < n := mem_range.mp hi
    have h := ((ih i hi').pow (p ^ (n - i))).C_mul ((p : ℚ) ^ i)
    rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le] at h
    exact h

end WittVector.WHomog

theorem solution
    (p : ℕ) [Fact p.Prime] {idx : Type v} (Φ : MvPolynomial idx ℤ) (k : ℕ) (hΦ : Φ.IsHomogeneous k)
    (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun bi : idx × ℕ => p ^ bi.2) (wittStructureInt p Φ n)
      (k * p ^ n) := by
  intro d hd
  have hΦ' : (MvPolynomial.map (Int.castRingHom ℚ) Φ).IsHomogeneous k := hΦ.map _
  have h := WittVector.WHomog.isWH_wittStructureRat p _ k hΦ' n
  rw [← map_wittStructureInt] at h
  refine h ?_
  rw [MvPolynomial.coeff_map]
  intro h0
  simp only [eq_intCast, Int.cast_eq_zero] at h0
  exact hd h0

end S_WittVector_isWeightedHomogeneous_wittStructureInt
end P2MW
export P2MW.S_WittVector_isWeightedHomogeneous_wittStructureInt (solution)
