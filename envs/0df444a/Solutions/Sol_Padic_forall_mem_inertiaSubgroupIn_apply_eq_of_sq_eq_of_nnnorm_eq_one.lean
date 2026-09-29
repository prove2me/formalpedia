-- Prove2me | solution 1 for Padic.forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d03de7e7-f59f-5aa5-9f23-6efd3b9d3b3f

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one

open scoped NNReal Pointwise

namespace E87GS

theorem apply_mem_and_sub_mem_nonunits_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    (a : L) (ha : a ∈ A) :
    τ a ∈ A ∧ τ a - a ∈ A.nonunits := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hτ
  have hgA : (g : L ≃ₐ[K] L) • A = A := g.2
  have hmem : (g : L ≃ₐ[K] L) a ∈ A := by
    have : (g : L ≃ₐ[K] L) • a ∈ (g : L ≃ₐ[K] L) • (A : ValuationSubring L) :=
      Set.smul_mem_smul_set (a := (g : L ≃ₐ[K] L)) ha
    rw [hgA] at this
    exact this
  refine ⟨hmem, ?_⟩
  have hker := (MonoidHom.mem_ker).mp hg
  have hres : IsLocalRing.residue A (g • (⟨a, ha⟩ : A)) = IsLocalRing.residue A ⟨a, ha⟩ := by
    have h1 := congrArg (fun φ => φ (IsLocalRing.residue A ⟨a, ha⟩)) hker
    simpa using h1
  have hsub : g • (⟨a, ha⟩ : A) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hres
  have hcoe : ((g • (⟨a, ha⟩ : A) - ⟨a, ha⟩ : A) : L) = (g : L ≃ₐ[K] L) a - a := rfl
  rw [← ValuationSubring.coe_mem_nonunits_iff, hcoe] at hsub
  exact hsub

variable (p : ℕ) [Fact p.Prime]

theorem main (hp2 : p ≠ 2) (d : ℚ_[p]) (hd : ‖d‖₊ = 1)
    (s : PadicAlgCl p) (hs : s ^ 2 = algebraMap ℚ_[p] (PadicAlgCl p) d) :
    ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → τ s = s := by
  intro τ hτ

  have hs1 : ‖s‖₊ = 1 := by
    have h := congrArg (fun x => ‖x‖₊) hs
    simp only [nnnorm_pow] at h
    rw [show ‖algebraMap ℚ_[p] (PadicAlgCl p) d‖₊ = ‖d‖₊ from by
      rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]; exact PadicAlgCl.norm_extends p d, hd] at h
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).mp h
  have hsA : s ∈ padicIntegers p := by rw [mem_padicIntegers_iff, hs1]
  obtain ⟨hτs, hdiff⟩ := apply_mem_and_sub_mem_nonunits_of_mem_inertiaSubgroupIn (padicIntegers p) hτ s hsA

  have hsq : (τ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, AlgEquiv.commutes]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
  · exact h
  · exfalso

    have h2 : τ s - s = -(2 : PadicAlgCl p) * s := by rw [h]; ring
    rw [h2] at hdiff
    have htwo : ‖(2 : PadicAlgCl p)‖₊ = 1 := by
      have : ((2 : PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) (2 : ℚ_[p]) := (map_ofNat _ 2).symm
      rw [this, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]
      erw [PadicAlgCl.norm_extends p (2 : ℚ_[p])]
      have h2' : ((2 : ℚ_[p])) = ((2 : ℕ) : ℚ_[p]) := by norm_num
      rw [h2', Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2
    have hnorm : ‖-(2 : PadicAlgCl p) * s‖₊ = 1 := by
      rw [nnnorm_mul, nnnorm_neg, hs1, mul_one, htwo]
    rcases (ValuationSubring.mem_nonunits_iff_or (padicIntegers p)).mp hdiff with h0 | hinv
    · have : ‖-(2 : PadicAlgCl p) * s‖₊ = 0 := by rw [h0, nnnorm_zero]
      rw [hnorm] at this
      exact one_ne_zero this
    · apply hinv
      rw [mem_padicIntegers_iff, nnnorm_inv, hnorm, inv_one]

end E87GS

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (d : ℚ_[p]) (hd : ‖d‖₊ = 1)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d) :
    ∀ τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
      τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → τ s = s :=
  E87GS.main p hp2 d hd s hs

end S_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one
end P2MW
export P2MW.S_Padic_forall_mem_inertiaSubgroupIn_apply_eq_of_sq_eq_of_nnnorm_eq_one (solution)
