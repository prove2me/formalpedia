-- Prove2me | solution 1 for ValuationSubring.apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1f6630e9-abbe-506d-8bad-42f437fc0cef

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped Pointwise

namespace GaloisRep
namespace SolE747

section Val
variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

theorem valuation_eq_one_of_pow_eq_one {x : L} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : A.valuation x = 1 := by
  have h : A.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  rcases lt_trichotomy (A.valuation x) 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hlt hn))
  · exact heq
  · exact absurd h (ne_of_gt (one_lt_pow₀ hgt hn))

theorem valuation_natCast_eq_one_of_coprime {q m : ℕ} (hq : A.valuation (q : L) < 1) (hm : Nat.Coprime m q) :
    A.valuation (m : L) = 1 := by
  have hle : A.valuation (m : L) ≤ 1 := by rw [ValuationSubring.valuation_le_one_iff]; exact natCast_mem A m
  by_contra hne
  have hlt : A.valuation (m : L) < 1 := lt_of_le_of_ne hle hne
  have hg : (Int.gcd m q : ℤ) = 1 := by exact_mod_cast hm
  have hb := Int.gcd_eq_gcd_ab m q
  rw [hg] at hb
  have h1 : (1 : L) = (m : L) * (Int.gcdA m q : L) + (q : L) * (Int.gcdB m q : L) := by
    exact_mod_cast congrArg (Int.cast : ℤ → L) hb
  have : A.valuation (1 : L) < 1 := by
    rw [h1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hlt (by rw [ValuationSubring.valuation_le_one_iff]; exact intCast_mem A _)
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hq (by rw [ValuationSubring.valuation_le_one_iff]; exact intCast_mem A _)
  rw [map_one] at this
  exact lt_irrefl _ this

theorem eq_one_of_pow_eq_one_of_valuation_sub_one_lt {q n : ℕ} (hq : A.valuation (q : L) < 1) (hn : Nat.Coprime n q)
    {η : L} (hηn : η ^ n = 1) (hη : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne

  have hgeom : (Finset.range n).sum (fun j => η ^ j) = 0 := by
    have h := geom_sum_mul η n
    rw [hηn, sub_self, mul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero.mpr hne)

  have hpow : ∀ j : ℕ, A.valuation (η ^ j - 1) < 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : η ^ (j + 1) - 1 = η * (η ^ j - 1) + (η - 1) := by ring
      rw [this]
      refine Valuation.map_add_lt _ ?_ hη
      rw [map_mul, valuation_eq_one_of_pow_eq_one A (fun h0 => ?_) hηn, one_mul]
      · exact ih
      · subst h0; simp at hn; subst hn; simp at hq
  have hsum : A.valuation ((Finset.range n).sum (fun j => η ^ j) - n) < 1 := by
    have : (Finset.range n).sum (fun j => η ^ j) - n = (Finset.range n).sum (fun j => (η ^ j - 1)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [this]
    exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hpow j)
  rw [hgeom, zero_sub, Valuation.map_neg, valuation_natCast_eq_one_of_coprime A hq hn] at hsum
  exact lt_irrefl _ hsum

end Val

section Inertia
variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) : A.valuation (σ x - x) < 1 := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) d = 1 := hd
  have h1 : (d • (IsLocalRing.residue A ⟨x, hx⟩) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ⟨x, hx⟩ := by
    have := RingEquiv.congr_fun hker (IsLocalRing.residue A ⟨x, hx⟩)
    simpa using this

  have h2 : (d • (IsLocalRing.residue A ⟨x, hx⟩) : IsLocalRing.ResidueField A) = IsLocalRing.residue A (d • ⟨x, hx⟩) := rfl
  rw [h2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
  have h3 := (ValuationSubring.valuation_lt_one_iff A _).mp h1
  exact h3

end Inertia

section Cyclo
variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

theorem valuation_one_sub_eq {q : ℕ} (hq : q.Prime) {ζ μ : L} (hζ : IsPrimitiveRoot ζ q) (hμ : IsPrimitiveRoot μ q) :
    A.valuation (1 - μ) = A.valuation (1 - ζ) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have key : ∀ {a b : L}, IsPrimitiveRoot a q → b ^ q = 1 → A.valuation (1 - b) ≤ A.valuation (1 - a) := by
    intro a b ha hb
    obtain ⟨i, -, rfl⟩ := ha.eq_pow_of_pow_eq_one hb
    have hgs : 1 - a ^ i = (1 - a) * (Finset.range i).sum (fun j => a ^ j) := by
      have h := mul_geom_sum a i
      linear_combination h
    rw [hgs, map_mul]
    refine mul_le_of_le_one_right' ?_
    refine Valuation.map_sum_le _ (fun j _ => ?_)
    rw [map_pow, valuation_eq_one_of_pow_eq_one A hq.ne_zero ha.pow_eq_one, one_pow]
  exact le_antisymm (key hζ hμ.pow_eq_one) (key hμ hζ.pow_eq_one)

theorem valuation_natCast_eq_pow {q : ℕ} (hq : q.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ q) :
    A.valuation (q : L) = A.valuation (1 - ζ) ^ (q - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h := Polynomial.eval_one_cyclotomic_prime (R := L) (p := q)
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  rw [← h, map_prod, Finset.prod_congr rfl (fun μ hμ => valuation_one_sub_eq A hq hζ ((mem_primitiveRoots hq.pos).mp hμ)),
    Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime hq]

end Cyclo

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem apply_root_eq_self_of_cyc_eq_one {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (cyc : Γℚ →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : Γℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 → σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : Γℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1)
    (α : AlgebraicClosure ℚ) (hα : α ^ (q - 1) = (q : AlgebraicClosure ℚ)) :
    σ α = α := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  have hvq : P.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff P).mp hP

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ q := HasEnoughRootsOfUnity.prim
  have hσζ : σ ζ = ζ := by
    rw [hcyc σ ζ hζ.pow_eq_one, hσc, Units.val_one, ZMod.val_one, pow_one]
  have hζ1 : (1 : AlgebraicClosure ℚ) - ζ ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hq.one_lt).symm

  set u : AlgebraicClosure ℚ := (q : AlgebraicClosure ℚ) / (1 - ζ) ^ (q - 1) with hu
  set β : AlgebraicClosure ℚ := α / (1 - ζ) with hβ
  have hσu : σ u = u := by
    rw [hu, map_div₀, map_pow, map_sub, map_one, hσζ, map_natCast]
  have hβu : β ^ (q - 1) = u := by rw [hβ, div_pow, hα]
  have hvu : P.valuation u = 1 := by
    rw [hu, map_div₀, map_pow, valuation_natCast_eq_pow P hq hζ, div_self]
    exact pow_ne_zero _ ((map_ne_zero _).mpr hζ1)
  have hq1 : q - 1 ≠ 0 := (Nat.sub_pos_of_lt hq.one_lt).ne'
  have hvβ : P.valuation β = 1 := by
    have h : P.valuation β ^ (q - 1) = 1 := by rw [← map_pow, hβu, hvu]
    rcases lt_trichotomy (P.valuation β) 1 with hlt | heq | hgt
    · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hlt hq1))
    · exact heq
    · exact absurd h (ne_of_gt (one_lt_pow₀ hgt hq1))
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hvβ; exact zero_ne_one hvβ
  have hβP : β ∈ P := (P.valuation_le_one_iff β).mp hvβ.le

  have hin : P.valuation (σ β - β) < 1 := valuation_sub_lt_one_of_mem_inertiaSubgroupIn P hσ hβP
  set η : AlgebraicClosure ℚ := σ β / β with hη
  have hηpow : η ^ (q - 1) = 1 := by
    rw [hη, div_pow, ← map_pow, hβu, hσu, div_self]
    rw [← hβu]; exact pow_ne_zero _ hβ0
  have hηv : P.valuation (η - 1) < 1 := by
    have : η - 1 = (σ β - β) / β := by rw [hη, sub_div, div_self hβ0]
    rw [this, map_div₀, hvβ, div_one]
    exact hin
  have hcop : Nat.Coprime (q - 1) q := by
    have : Nat.Coprime (q - 1 + 1) (q - 1) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
    rw [Nat.sub_add_cancel hq.one_lt.le] at this
    exact this.symm
  have hη1 : η = 1 := eq_one_of_pow_eq_one_of_valuation_sub_one_lt P hvq hcop hηpow hηv
  have hσβ : σ β = β := by rwa [hη, div_eq_one_iff_eq hβ0] at hη1

  have hαβ : α = β * (1 - ζ) := by rw [hβ, div_mul_cancel₀ _ hζ1]
  rw [hαβ, map_mul, hσβ, map_sub, map_one, hσζ]

end GaloisRep.SolE747

open GaloisRep.SolE747 in
theorem solution {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hσc : cyc σ = 1)
    (α : AlgebraicClosure ℚ) (hα : α ^ (q - 1) = (q : AlgebraicClosure ℚ)) :
    σ α = α :=
  apply_root_eq_self_of_cyc_eq_one hq P hP cyc hcyc hσ hσc α hα

end S_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one
end P2MW
export P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_prime_of_mem_inertiaSubgroupIn_of_cyc_eq_one (solution)
