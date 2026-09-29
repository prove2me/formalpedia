-- Prove2me | solution 1 for WeierstrassCurve.valuation_c4_add_veluTSum_lt_one_of_formal_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6f0955f1-ae63-5587-b759-09a470b5a0aa

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_WeierstrassCurve_addX_self_sub_mul_sq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre
import Theorems.Thm_cyclotomic_velu_powerSums
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_valuation_c4_add_veluTSum_lt_one_of_formal_kernel
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

namespace FormalC4Aux

section QUnit

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma not_mem_iff_one_lt_valuation {x : AlgebraicClosure ℚ} :
    x ∉ A ↔ 1 < A.valuation x := by
  rw [← A.valuation_le_one_iff x, not_le]

private lemma valuation_natCast_lt_one {q : ℕ} (hA : A.LiesOverPrime q) :
    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := hA

private lemma valuation_intCast_eq_one_of_not_dvd {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) :
    A.valuation ((n : ℤ) : AlgebraicClosure ℚ) = 1 := by
  have hqK : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp (by simpa using hqK)
  have hunit : IsUnit ((n : ℤ) : A) := by
    by_contra hunit
    have hmem : ((n : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal]; exact hunit
    obtain ⟨a, b, hab⟩ := (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hn
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hh := congrArg (fun z : ℤ => ((z : ℤ) : A)) hab
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at hh
      rw [← hh]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqmem) (Ideal.mul_mem_left _ _ hmem)
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  simpa using (A.valuation_eq_one_iff _).mp hunit

end QUnit

section Step0

private lemma step0_q_eq_p (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {p : ℕ} (hp : p.Prime) {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hQord : addOrderOf (Point.some x y h) = p) (hx : x ∉ A) : q = p := by
  by_contra hqp
  have hqn : ¬ q ∣ p := fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd)
  have hP : p • (Point.some x y h) = 0 := by
    rw [← hQord]; exact addOrderOf_nsmul_eq_zero _
  rcases W.torsion_integral_of_not_dvd hq A hA hqn (Point.some x y h) hP with h0 |
    ⟨x', y', h', heq, hx', -⟩
  · exact some_ne_zero h h0
  · rw [Point.some.injEq] at heq
    exact hx (heq.1 ▸ hx')

end Step0

section Pigeonhole

open Polynomial

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private lemma exists_primitiveRoot (p : ℕ) (hp : p.Prime) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := by
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  have hdeg : (cyclotomic p (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, isRoot_cyclotomic_iff.mp hζ⟩

private lemma isPrimitiveRoot_of_pow_eq_one {p : ℕ} (hp : p.Prime)
    {η : AlgebraicClosure ℚ} (hpow : η ^ p = 1) (hη1 : η ≠ 1) : IsPrimitiveRoot η p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf η = p := orderOf_eq_prime hpow hη1
  exact ⟨hpow, fun l hl => hord ▸ orderOf_dvd_of_pow_eq_one hl⟩

private lemma pow_left_inj' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hlt (zero_le' (a := a)) hn))
  · exact heq
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_left₀ hgt (zero_le' (a := b)) hn))

private lemma valuation_eq_one_of_pow_eq_one {p : ℕ} (hp : 0 < p)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ p = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ p = 1 ^ p := by
    rw [← map_pow, hζ, map_one, one_pow]
  exact pow_left_inj' hp.ne' h

private lemma valuation_one_sub_pow_le {ζ : AlgebraicClosure ℚ}
    (hv : A.valuation ζ = 1) (k : ℕ) :
    A.valuation (1 - ζ ^ k) ≤ A.valuation (1 - ζ) := by
  have hgeom : (1 - ζ) * ∑ i ∈ Finset.range k, ζ ^ i = 1 - ζ ^ k := by
    have h := mul_geom_sum ζ k
    linear_combination -h
  rw [← hgeom, map_mul]
  have hsum : A.valuation (∑ i ∈ Finset.range k, ζ ^ i) ≤ 1 :=
    Valuation.map_sum_le _ fun i _ => by rw [map_pow, hv, one_pow]
  calc A.valuation (1 - ζ) * A.valuation (∑ i ∈ Finset.range k, ζ ^ i)
      ≤ A.valuation (1 - ζ) * 1 := mul_le_mul_right hsum _
    _ = A.valuation (1 - ζ) := mul_one _

private lemma valuation_one_sub_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime)
    {η μ : AlgebraicClosure ℚ} (hη : η ^ p = 1) (hη1 : η ≠ 1)
    (hμ : μ ^ p = 1) (hμ1 : μ ≠ 1) :
    A.valuation (1 - μ) = A.valuation (1 - η) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, _, hi⟩ := (isPrimitiveRoot_of_pow_eq_one hp hη hη1).eq_pow_of_pow_eq_one hμ
  obtain ⟨j, _, hj⟩ := (isPrimitiveRoot_of_pow_eq_one hp hμ hμ1).eq_pow_of_pow_eq_one hη
  refine le_antisymm ?_ ?_
  · rw [← hi]
    exact valuation_one_sub_pow_le A (valuation_eq_one_of_pow_eq_one A hp.pos hη) i
  · rw [← hj]
    exact valuation_one_sub_pow_le A (valuation_eq_one_of_pow_eq_one A hp.pos hμ) j

private lemma prod_one_sub_nthRoots_eq (p : ℕ) (hp : p.Prime) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ p) :
    ∏ η ∈ (nthRootsFinset p (1 : AlgebraicClosure ℚ)).erase 1, (1 - η)
      = ((p : ℕ) : AlgebraicClosure ℚ) := by
  have hsplit : (X : Polynomial (AlgebraicClosure ℚ)) ^ p - 1
      = (X - C 1) * ∏ η ∈ (nthRootsFinset p (1 : AlgebraicClosure ℚ)).erase 1, (X - C η) := by
    rw [X_pow_sub_one_eq_prod hp.pos hζ,
      ← Finset.mul_prod_erase _ _ (one_mem_nthRootsFinset hp.pos)]
  have hgeom : (X : Polynomial (AlgebraicClosure ℚ)) ^ p - 1
      = (X - C 1) * ∑ i ∈ Finset.range p, (X : Polynomial (AlgebraicClosure ℚ)) ^ i := by
    rw [C_1]
    exact (mul_geom_sum _ p).symm
  have hcancel : (∑ i ∈ Finset.range p, (X : Polynomial (AlgebraicClosure ℚ)) ^ i)
      = ∏ η ∈ (nthRootsFinset p (1 : AlgebraicClosure ℚ)).erase 1, (X - C η) :=
    mul_left_cancel₀ (X_sub_C_ne_zero 1) (hgeom.symm.trans hsplit)
  have heval := congrArg (Polynomial.eval (1 : AlgebraicClosure ℚ)) hcancel
  simpa [Polynomial.eval_prod, Polynomial.eval_finsetSum] using heval.symm

private lemma exists_primitiveRoot_valuation_close {p : ℕ} (hp : p.Prime)
    {w : AlgebraicClosure ℚ}
    (hB : A.valuation (w ^ p - 1) <
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) * A.valuation (w - 1)) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p ∧
      A.valuation (w - ζ) < A.valuation (1 - ζ) ∧
      A.valuation (1 - ζ) = A.valuation (w - 1) ∧
      A.valuation (w - ζ) * A.valuation ((p : ℕ) : AlgebraicClosure ℚ)
        = A.valuation (w ^ p - 1) ∧
      ∀ j : ℕ, ¬ p ∣ j → A.valuation (1 - ζ ^ j) = A.valuation (w - 1) := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot p hp
  set N := nthRootsFinset p (1 : AlgebraicClosure ℚ) with hNdef
  have h1N : (1 : AlgebraicClosure ℚ) ∈ N := one_mem_nthRootsFinset hp.pos

  have hfact : w ^ p - 1 = ∏ η ∈ N, (w - η) := by
    have h := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hp.pos hζ₀)
    simpa [Polynomial.eval_prod] using h
  have hvfact : A.valuation (w ^ p - 1)
      = A.valuation (w - 1) * ∏ η ∈ N.erase 1, A.valuation (w - η) := by
    rw [hfact, map_prod, ← Finset.mul_prod_erase _ _ h1N]

  have hmemN : ∀ η ∈ N.erase 1, η ^ p = 1 ∧ η ≠ 1 := fun η hη =>
    ⟨(mem_nthRootsFinset hp.pos 1).mp (Finset.mem_of_mem_erase hη), Finset.ne_of_mem_erase hη⟩

  have hc₀ : ∀ η ∈ N.erase 1, A.valuation (1 - η) = A.valuation (1 - ζ₀) := by
    intro η hη
    obtain ⟨hpow, hne⟩ := hmemN η hη
    exact valuation_one_sub_eq_of_pow_eq_one A hp hζ₀.pow_eq_one (hζ₀.ne_one hp.one_lt) hpow hne
  have hcardN : N.card = p := hζ₀.card_nthRootsFinset
  have hcard1 : (N.erase 1).card = p - 1 := by
    rw [Finset.card_erase_of_mem h1N, hcardN]
  have hvp : A.valuation (1 - ζ₀) ^ (p - 1)
      = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) := by
    rw [← prod_one_sub_nthRoots_eq p hp hζ₀, map_prod, Finset.prod_congr rfl hc₀,
      Finset.prod_const, hcard1]

  by_cases hall : ∀ η ∈ N.erase 1, A.valuation (1 - η) ≤ A.valuation (w - η)
  · exfalso
    have hge : A.valuation ((p : ℕ) : AlgebraicClosure ℚ)
        ≤ ∏ η ∈ N.erase 1, A.valuation (w - η) := by
      rw [← hvp, ← hcard1, ← Finset.prod_const]
      exact Finset.prod_le_prod' fun η hη => (hc₀ η hη) ▸ hall η hη
    have hcontra : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) * A.valuation (w - 1)
        ≤ A.valuation (w ^ p - 1) := by
      rw [hvfact, mul_comm (A.valuation (w - 1))]
      exact mul_le_mul' hge le_rfl
    exact absurd hB (not_lt.mpr hcontra)
  · push Not at hall
    obtain ⟨ζ, hζN, hclose⟩ := hall
    obtain ⟨hζpow, hζne1⟩ := hmemN ζ hζN
    have hζprim : IsPrimitiveRoot ζ p := isPrimitiveRoot_of_pow_eq_one hp hζpow hζne1
    have hζ0 : ζ ≠ 0 := fun h => by
      rw [h, zero_pow hp.ne_zero] at hζpow; exact zero_ne_one hζpow

    have hcloseC : A.valuation (w - ζ) < A.valuation (1 - ζ₀) := (hc₀ ζ hζN) ▸ hclose

    have hw1c : A.valuation (w - 1) = A.valuation (1 - ζ₀) := by
      have hne' : A.valuation (w - ζ) ≠ A.valuation (ζ - 1) := by
        rw [A.valuation.map_sub_swap ζ 1, hc₀ ζ hζN]
        exact ne_of_lt hcloseC
      rw [show w - 1 = (w - ζ) + (ζ - 1) by ring,
        Valuation.map_add_of_distinct_val _ hne', A.valuation.map_sub_swap ζ 1, hc₀ ζ hζN]
      exact max_eq_right (le_of_lt hcloseC)

    have hother : ∀ η ∈ (N.erase 1).erase ζ,
        A.valuation (w - η) = A.valuation (1 - ζ₀) := by
      intro η hη
      have hηN : η ∈ N.erase 1 := Finset.mem_of_mem_erase hη
      have hηζ : η ≠ ζ := Finset.ne_of_mem_erase hη
      obtain ⟨hηpow, hηne1⟩ := hmemN η hηN
      have hμpow : (ζ⁻¹ * η) ^ p = 1 := by
        rw [mul_pow, inv_pow, hζpow, hηpow, inv_one, one_mul]
      have hμne1 : ζ⁻¹ * η ≠ 1 := fun h => hηζ (by
        have h2 : ζ * (ζ⁻¹ * η) = ζ * 1 := by rw [h]
        rwa [← mul_assoc, mul_inv_cancel₀ hζ0, one_mul, mul_one] at h2)
      have hμN : ζ⁻¹ * η ∈ N.erase 1 :=
        Finset.mem_erase.mpr ⟨hμne1, (mem_nthRootsFinset hp.pos 1).mpr hμpow⟩
      have hfactored : ζ - η = ζ * (1 - ζ⁻¹ * η) := by
        rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
      have hvζη : A.valuation (ζ - η) = A.valuation (1 - ζ₀) := by
        rw [hfactored, map_mul, valuation_eq_one_of_pow_eq_one A hp.pos hζpow, one_mul]
        exact hc₀ _ hμN
      have hne' : A.valuation (w - ζ) ≠ A.valuation (ζ - η) := by
        rw [hvζη]; exact ne_of_lt hcloseC
      rw [show w - η = (w - ζ) + (ζ - η) by ring,
        Valuation.map_add_of_distinct_val _ hne', hvζη]
      exact max_eq_right (le_of_lt hcloseC)

    have hcard2 : ((N.erase 1).erase ζ).card = p - 2 := by
      rw [Finset.card_erase_of_mem hζN, hcard1]
      omega
    have hprod2 : ∏ η ∈ (N.erase 1).erase ζ, A.valuation (w - η)
        = A.valuation (1 - ζ₀) ^ (p - 2) := by
      rw [Finset.prod_congr rfl hother, Finset.prod_const, hcard2]
    have hexact : A.valuation (w - ζ) * A.valuation ((p : ℕ) : AlgebraicClosure ℚ)
        = A.valuation (w ^ p - 1) := by
      rw [hvfact, ← Finset.mul_prod_erase _ _ hζN, hprod2, hw1c, ← hvp]
      have hpp : p - 1 = (p - 2) + 1 := by have := hp.two_le; omega
      rw [hpp, pow_succ, ← mul_assoc,
        mul_comm (A.valuation (w - ζ) * A.valuation (1 - ζ₀) ^ (p - 2)) (A.valuation (1 - ζ₀))]
    refine ⟨ζ, hζprim, hclose, (hc₀ ζ hζN).trans hw1c.symm, hexact, ?_⟩
    intro j hj
    have hjpow : (ζ ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζpow, one_pow]
    have hjne : ζ ^ j ≠ 1 := fun h => hj (hζprim.dvd_of_pow_eq_one j h)
    rw [valuation_one_sub_eq_of_pow_eq_one A hp hζ₀.pow_eq_one (hζ₀.ne_one hp.one_lt) hjpow hjne]
    exact hw1c.symm

private lemma valuation_pow_sub_pow_le {w ζ : AlgebraicClosure ℚ}
    (hw : A.valuation w = 1) (hζ : A.valuation ζ = 1) (k : ℕ) :
    A.valuation (w ^ k - ζ ^ k) ≤ A.valuation (w - ζ) := by
  have hgeom : (w - ζ) * ∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i) = w ^ k - ζ ^ k :=
    Commute.mul_geom_sum₂ (Commute.all w ζ) k
  rw [← hgeom, map_mul]
  have hsum : A.valuation (∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i)) ≤ 1 :=
    Valuation.map_sum_le _ fun i _ => by rw [map_mul, map_pow, map_pow, hw, hζ]; simp
  calc A.valuation (w - ζ) * A.valuation (∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i))
      ≤ A.valuation (w - ζ) * 1 := mul_le_mul' le_rfl hsum
    _ = A.valuation (w - ζ) := mul_one _

end Pigeonhole

section CurveDock

local notation "Kb" => AlgebraicClosure ℚ

variable (W : WeierstrassCurve ℤ)

private lemma psisq_expand {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {x y : Kb}
    (heq : y ^ 2 + (W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y
      = x ^ 3 + (W.a₂ : Kb) * x ^ 2 + (W.a₄ : Kb) * x + (W.a₆ : Kb)) :
    (2 * y + (W.a₁ : Kb) * x + W.a₃) ^ 2
      = ((W.b₂ : Kb) + 12 * x₀) * (x - x₀) ^ 2 + 4 * (x - x₀) ^ 3
        - 4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
            - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  simp only [b₂]
  push_cast
  linear_combination (4 : Kb) * heq
    + ((2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃) + 2 * (W.a₁ : Kb) * (x - x₀)) * hFy
    - 4 * (x - x₀) * hFx

private lemma equation_cast {x y : Kb}
    (h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y) :
    y ^ 2 + (W.a₁ : Kb) * x * y + (W.a₃ : Kb) * y
      = x ^ 3 + (W.a₂ : Kb) * x ^ 2 + (W.a₄ : Kb) * x + (W.a₆ : Kb) := by
  have heq := h.1
  rw [Affine.equation_iff] at heq
  simpa only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
    Affine.baseChange_a₄, Affine.baseChange_a₆, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eq_intCast, map_intCast] using heq

private lemma negY_cast (x y : Kb) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y
      = -y - (W.a₁ : Kb) * x - (W.a₃ : Kb) := by
  simp only [Affine.negY, Affine.baseChange_a₁, Affine.baseChange_a₃,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast, map_intCast]

variable {W}

private lemma exists_kernel_coords {p : ℕ}
    {x y : Kb} {h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y}
    (hQord : addOrderOf (Point.some x y h) = p) :
    ∃ xc yc : ℕ → Kb, ∀ m, 1 ≤ m → m < p →
      ∃ hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xc m) (yc m),
        m • (Point.some x y h) = .some (xc m) (yc m) hm := by
  have hAff : ∀ m : ℕ, ∃ xm ym : Kb,
      (1 ≤ m → m < p →
        ∃ hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular xm ym,
          m • (Point.some x y h) = .some xm ym hm) := by
    intro m
    by_cases hrange : 1 ≤ m ∧ m < p
    · have hne : m • (Point.some x y h) ≠ 0 :=
        nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQord]; exact hrange.2)
      cases hmQ : m • (Point.some x y h) with
      | zero => exact absurd hmQ hne
      | some xm ym hm => exact ⟨xm, ym, fun _ _ => ⟨hm, rfl⟩⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hrange⟩
  choose xc yc hspec using hAff
  exact ⟨xc, yc, hspec⟩

private lemma exists_kernel_dock {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x₀ y₀ β ε : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hβ : β = (W.b₂ : Kb) + 12 * x₀)
    (hε : ε = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
    {x y : Kb} {h : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular x y}
    (hQord : addOrderOf (Point.some x y h) = p) :
    ∃ xc yc : ℕ → Kb,
      xc 1 = x ∧ yc 1 = y ∧
      (∀ m, 1 ≤ m → m < p →
        ∃ hm : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Nonsingular (xc m) (yc m),
          m • (Point.some x y h) = .some (xc m) (yc m) hm) ∧
      xc (p - 1) = xc 1 ∧
      ((xc 2 - x₀) * (4 * (xc 1 - x₀) ^ 3 + β * (xc 1 - x₀) ^ 2 - 4 * ε)
        = (xc 1 - x₀) ^ 4 + 8 * ε * (xc 1 - x₀) + β * ε) ∧
      (∀ m, 2 ≤ m → m ≤ p - 2 →
        (xc (m + 1) - x₀) * (xc (m - 1) - x₀) * ((xc m - x₀) - (xc 1 - x₀)) ^ 2
          = ((xc m - x₀) * (xc 1 - x₀)) ^ 2
            + ε * (4 * (xc m - x₀) + 4 * (xc 1 - x₀) + β)) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨xc, yc, hspec⟩ := exists_kernel_coords hQord

  obtain ⟨h1, heq1⟩ := hspec 1 le_rfl (by omega)
  rw [one_nsmul, Point.some.injEq] at heq1
  have hx1 : xc 1 = x := heq1.1.symm
  have hy1 : yc 1 = y := heq1.2.symm

  have hΨne : 2 * y + (W.a₁ : Kb) * x + W.a₃ ≠ 0 := by
    intro h0
    have hyneg : y = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y := by
      rw [negY_cast]
      linear_combination h0
    have h2Q : (2 : ℕ) • (Point.some x y h) = 0 := by
      rw [two_nsmul]
      exact Point.add_of_Y_eq rfl hyneg
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h2Q
    rw [hQord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

  have hpQ : p • (Point.some x y h) = 0 := by
    rw [← hQord]
    exact addOrderOf_nsmul_eq_zero _
  have hS : xc (p - 1) = xc 1 := by
    obtain ⟨hm, heqm⟩ := hspec (p - 1) (by omega) (by omega)
    have hSneg : (p - 1) • (Point.some x y h) = -(Point.some x y h) := by
      have hadd : (p - 1) • (Point.some x y h) + (Point.some x y h) = 0 := by
        rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
        exact hpQ
      exact eq_neg_of_add_eq_zero_left hadd
    rw [heqm, Point.neg_some, Point.some.injEq] at hSneg
    rw [hSneg.1, hx1]

  have hD : (xc 2 - x₀) * (4 * (xc 1 - x₀) ^ 3 + β * (xc 1 - x₀) ^ 2 - 4 * ε)
      = (xc 1 - x₀) ^ 4 + 8 * ε * (xc 1 - x₀) + β * ε := by
    obtain ⟨h2, heq2⟩ := hspec 2 (by omega) (by omega)
    have hxy' : ¬(x = x ∧ y = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y) := by
      rintro ⟨-, hy⟩
      apply hΨne
      rw [negY_cast] at hy
      linear_combination hy
    rw [two_nsmul] at heq2
    rw [Point.add_some hxy', Point.some.injEq] at heq2
    have hrow := W.addX_self_sub_mul_sq_of_criticalCentre hFy hFx h hΨne
    rw [heq2.1] at hrow
    have hψ := psisq_expand W hFy hFx (equation_cast W h)
    rw [hβ, hε, hx1]
    linear_combination hrow - (xc 2 - x₀) * hψ

  have hR : ∀ m, 2 ≤ m → m ≤ p - 2 →
      (xc (m + 1) - x₀) * (xc (m - 1) - x₀) * ((xc m - x₀) - (xc 1 - x₀)) ^ 2
        = ((xc m - x₀) * (xc 1 - x₀)) ^ 2
          + ε * (4 * (xc m - x₀) + 4 * (xc 1 - x₀) + β) := by
    intro m hm2 hmp2
    obtain ⟨hm, heqm⟩ := hspec m (by omega) (by omega)
    obtain ⟨hm1, heqm1⟩ := hspec (m + 1) (by omega) (by omega)
    obtain ⟨hm1', heqm1'⟩ := hspec (m - 1) (by omega) (by omega)

    have hdist : xc m ≠ x := by
      intro hxeq
      rcases (Point.X_eq_iff (h₁ := hm) (h₂ := h)).mp hxeq with hPQ | hPQ
      · have hzero : (m - 1) • (Point.some x y h) = 0 := by
          have hadd : m • (Point.some x y h)
              = (m - 1) • (Point.some x y h) + (Point.some x y h) := by
            rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
          rw [heqm, hPQ] at hadd
          have h0 : (0 : ((W.map (Int.castRingHom ℚ))⁄Kb).Point) + Point.some x y h
              = (m - 1) • (Point.some x y h) + Point.some x y h := by
            rw [zero_add]; exact hadd
          exact (add_right_cancel h0).symm
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hzero
        rw [hQord] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · have hzero : (m + 1) • (Point.some x y h) = 0 := by
          rw [succ_nsmul, heqm, hPQ, neg_add_cancel]
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hzero
        rw [hQord] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega

    have hside1 : ¬(xc m = x ∧ yc m = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y) :=
      fun hc => hdist hc.1
    have hext1 : xc (m + 1) = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.addX (xc m) x
        (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.slope (xc m) x (yc m) y) := by
      have hadd : (m + 1) • (Point.some x y h)
          = Point.some (xc m) (yc m) hm + Point.some x y h := by
        rw [succ_nsmul, heqm]
      rw [hadd, Point.add_some hside1, Point.some.injEq] at heqm1
      exact heqm1.1.symm

    have hside2 : ¬(xc m = x ∧ yc m = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x
        (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y)) := fun hc => hdist hc.1
    have hext2 : xc (m - 1) = ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.addX (xc m) x
        (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.slope (xc m) x (yc m)
          (((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.negY x y)) := by
      have hadd : m • (Point.some x y h)
          = (m - 1) • (Point.some x y h) + (Point.some x y h) := by
        rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
      have h1' : (m - 1) • (Point.some x y h) + (Point.some x y h)
          = Point.some (xc m) (yc m) hm := hadd.symm.trans heqm
      have h2' : (m - 1) • (Point.some x y h)
          = Point.some (xc m) (yc m) hm - Point.some x y h := eq_sub_iff_add_eq.mpr h1'
      rw [sub_eq_add_neg, Point.neg_some, Point.add_some hside2] at h2'
      rw [heqm1', Point.some.injEq] at h2'
      exact h2'.1
    have hrow := W.addX_sub_mul_addX_neg_sub_mul_sq_of_criticalCentre hFy hFx hm h hdist
    rw [← hext1, ← hext2] at hrow
    rw [hβ, hε, hx1]
    linear_combination hrow
  exact ⟨xc, yc, hx1, hy1, hspec, hS, hD, hR⟩

private lemma valuation_intCast_le_of_dvd (A : ValuationSubring Kb) {q : ℕ} {n : ℤ}
    (hdvd : (q : ℤ) ∣ n) :
    A.valuation ((n : ℤ) : Kb) ≤ A.valuation ((q : ℕ) : Kb) := by
  obtain ⟨d, hd⟩ := hdvd
  have hdmem : A.valuation ((d : ℤ) : Kb) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (intCast_mem A d)
  calc A.valuation ((n : ℤ) : Kb)
      = A.valuation ((q : ℕ) : Kb) * A.valuation ((d : ℤ) : Kb) := by
        rw [← map_mul]
        congr 1
        push_cast [hd]
        ring
    _ ≤ A.valuation ((q : ℕ) : Kb) * 1 := mul_le_mul' le_rfl hdmem
    _ = A.valuation ((q : ℕ) : Kb) := mul_one _

private lemma hB_of_closure (A : ValuationSubring Kb) {p : ℕ} {w ε : Kb}
    (hcl : A.valuation (w ^ p - 1)
      ≤ A.valuation ε * A.valuation (w - 1) ^ 7)
    (hεp : A.valuation ε ≤ A.valuation ((p : ℕ) : Kb))
    (hp0 : A.valuation ((p : ℕ) : Kb) ≠ 0)
    (hτ0 : 0 < A.valuation (w - 1)) (hτ1 : A.valuation (w - 1) < 1) :
    A.valuation (w ^ p - 1)
      < A.valuation ((p : ℕ) : Kb) * A.valuation (w - 1) := by
  have h1 : A.valuation ε * A.valuation (w - 1) ^ 7
      ≤ A.valuation ((p : ℕ) : Kb) * A.valuation (w - 1) ^ 7 :=
    mul_le_mul' hεp le_rfl
  have h7 : A.valuation (w - 1) ^ 7 < A.valuation (w - 1) := by
    have := pow_lt_pow_right_of_lt_one₀ hτ0 hτ1 (by omega : 1 < 7)
    simpa using this
  have h2 : A.valuation (w - 1) ^ 7 * A.valuation ((p : ℕ) : Kb)
      < A.valuation (w - 1) * A.valuation ((p : ℕ) : Kb) :=
    (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hp0)).mpr h7
  calc A.valuation (w ^ p - 1)
      ≤ A.valuation ε * A.valuation (w - 1) ^ 7 := hcl
    _ ≤ A.valuation ((p : ℕ) : Kb) * A.valuation (w - 1) ^ 7 := h1
    _ = A.valuation (w - 1) ^ 7 * A.valuation ((p : ℕ) : Kb) := mul_comm _ _
    _ < A.valuation (w - 1) * A.valuation ((p : ℕ) : Kb) := h2
    _ = A.valuation ((p : ℕ) : Kb) * A.valuation (w - 1) := mul_comm _ _

private lemma valuation_w_sub_zeta_le (A : ValuationSubring Kb) {p : ℕ} {w ζ ε : Kb}
    (hprod : A.valuation (w - ζ) * A.valuation ((p : ℕ) : Kb) = A.valuation (w ^ p - 1))
    (hcl : A.valuation (w ^ p - 1) ≤ A.valuation ε * A.valuation (w - 1) ^ 7)
    (hεp : A.valuation ε ≤ A.valuation ((p : ℕ) : Kb))
    (hp0 : A.valuation ((p : ℕ) : Kb) ≠ 0) :
    A.valuation (w - ζ) ≤ A.valuation (w - 1) ^ 7 := by
  have h1 : A.valuation (w - ζ) * A.valuation ((p : ℕ) : Kb)
      ≤ A.valuation (w - 1) ^ 7 * A.valuation ((p : ℕ) : Kb) := by
    calc A.valuation (w - ζ) * A.valuation ((p : ℕ) : Kb)
        = A.valuation (w ^ p - 1) := hprod
      _ ≤ A.valuation ε * A.valuation (w - 1) ^ 7 := hcl
      _ ≤ A.valuation ((p : ℕ) : Kb) * A.valuation (w - 1) ^ 7 := mul_le_mul' hεp le_rfl
      _ = A.valuation (w - 1) ^ 7 * A.valuation ((p : ℕ) : Kb) := mul_comm _ _
  exact le_of_mul_le_mul_right h1 (zero_lt_iff.mpr hp0)

end CurveDock

section SummingSetGlue

variable {F : Type*} [Field F] [DecidableEq F] (W' : WeierstrassCurve F)

private lemma coords_inj_on_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Set ℕ) := by
  intro k hk k' hk' hcoords
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have hkne : k • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk.1 hd) (by omega)
  have hk'ne : k' • Q ≠ 0 := fun h0 => by
    have hd : p ∣ k' := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    exact absurd (Nat.le_of_dvd hk'.1 hd) (by omega)
  have hpt : k • Q = k' • Q := by
    cases hkQ : k • Q with
    | zero => exact absurd hkQ hkne
    | some xk yk hknon =>
      cases hk'Q : k' • Q with
      | zero => exact absurd hk'Q hk'ne
      | some xk' yk' hk'non =>
        simp only [hkQ, hk'Q, Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hcoords
        obtain ⟨rfl, rfl⟩ := hcoords
        rfl
  have hz : (p : ℤ) ∣ ((k : ℤ) - k') := by
    have h0 : ((k : ℤ) - k') • Q = 0 := by
      rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hpt]; exact sub_self _
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
    rw [hord] at this
    exact_mod_cast this
  have habs : |(k : ℤ) - (k' : ℤ)| < p := by
    have h1 : (k : ℤ) - k' < p := by omega
    have h2 : (k' : ℤ) - k < p := by omega
    rw [abs_sub_lt_iff]; omega
  have hsub0 : (k : ℤ) - k' = 0 := Int.eq_zero_of_abs_lt_dvd hz habs
  omega

private lemma veluTSum_eq_sum_Icc {Q : W'.toAffine.Point} {p n : ℕ}
    (hord : addOrderOf Q = p) (hn : 2 * n < p) :
    W'.veluTSum (W'.oddOrderSummingSet Q n)
      = ∑ k ∈ Finset.Icc 1 n, W'.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 := by
  rw [veluTSum, oddOrderSummingSet, Finset.sum_image]
  intro k hk k' hk' h
  exact coords_inj_on_Icc W' hord hn (Finset.mem_coe.mpr hk) (Finset.mem_coe.mpr hk') h

end SummingSetGlue

section CentreT

local notation "Kb" => AlgebraicClosure ℚ

private theorem veluT_factor (W : WeierstrassCurve ℤ) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) (x y : Kb) :
    ((W.map (Int.castRingHom ℚ))⁄Kb).veluT x y
      = (x - x₀) * (((W.b₂ : Kb) + 12 * x₀) + 6 * (x - x₀)) := by
  simp only [veluT, veluGx, veluGy, Affine.baseChange_a₁, Affine.baseChange_a₂,
    Affine.baseChange_a₃, Affine.baseChange_a₄, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    eq_intCast, map_intCast]
  have hb₂ : ((W.b₂ : ℤ) : Kb) = (W.a₁ : Kb) ^ 2 + 4 * W.a₂ := by simp [WeierstrassCurve.b₂]
  rw [hb₂]
  linear_combination (-2) * hFx + (W.a₁ : Kb) * hFy

end CentreT

section PSumsTarget

private theorem one_add_240_zsum_eq_pow_four {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    1 + 240 * ∑ k ∈ Finset.Icc 1 (p / 2),
        (ζ ^ k / (1 - ζ ^ k) ^ 2 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2) = (p : F) ^ 4 := by
  obtain ⟨h1, h2, -⟩ := cyclotomic_velu_powerSums hp hp2 hζ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h1440 : (1440 : F) ≠ 0 := by norm_num
  field_simp
  ring

end PSumsTarget

section TargetRewrite

local notation "Kb" => AlgebraicClosure ℚ

private theorem c₄_add_240T_eq_centred (W : WeierstrassCurve ℤ) {x₀ y₀ : Kb}
    (hFy : 2 * y₀ + (W.a₁ : Kb) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : Kb) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    {p : ℕ} {Q : ((W.map (Int.castRingHom ℚ))⁄Kb).toAffine.Point}
    (hQord : addOrderOf Q = p) {n : ℕ} (hn : 2 * n < p) :
    let β := (W.b₂ : Kb) + 12 * x₀
    let Xk : ℕ → Kb := fun k => (k • Q).coordsOrZero.1 - x₀
    (W.c₄ : Kb) + 240 * ((W.map (Int.castRingHom ℚ))⁄Kb).veluTSum
        (((W.map (Int.castRingHom ℚ))⁄Kb).oddOrderSummingSet Q n)
      = β ^ 2 + 240 * β * (∑ k ∈ Finset.Icc 1 n, Xk k)
        + 1440 * ∑ k ∈ Finset.Icc 1 n, Xk k ^ 2 := by
  intro β Xk
  rw [veluTSum_eq_sum_Icc _ hQord hn]

  have hc₄ : (W.c₄ : Kb) = β ^ 2 := by
    simp only [β, c₄, b₂, b₄]
    push_cast
    linear_combination (-24 : Kb) * (W.a₁ : Kb) * hFy + 48 * hFx
  rw [hc₄]

  have ht : ∀ k ∈ Finset.Icc 1 n,
      ((W.map (Int.castRingHom ℚ))⁄Kb).veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
        = Xk k * (β + 6 * Xk k) := fun k _ =>
    veluT_factor W hFy hFx (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
  rw [Finset.sum_congr rfl ht]
  have hexp : ∀ k ∈ Finset.Icc 1 n,
      Xk k * (β + 6 * Xk k) = β * Xk k + 6 * Xk k ^ 2 := fun k _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end TargetRewrite

section Resummation

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

private lemma abscissa_sub_eq {a b : F} (ha : a ≠ 1) (hb : b ≠ 1) :
    a / (1 - a) ^ 2 - b / (1 - b) ^ 2 = (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
  have ha' : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hb' : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  field_simp
  ring

private lemma valuation_abscissa_sub_le {a b : F} (ha : a ≠ 1) (hb : b ≠ 1)
    {τ : Γ₀} (hτ : τ ≠ 0) (hva : v a = 1)
    (h1a : v (1 - a) = τ) (h1b : v (1 - b) = τ) :
    v (a / (1 - a) ^ 2 - b / (1 - b) ^ 2) * τ ^ 4 ≤ v (a - b) * τ := by
  rw [abscissa_sub_eq ha hb, map_div₀, map_mul, map_mul, map_pow, map_pow, h1a, h1b,
    ← pow_add, div_mul_cancel₀ _ (pow_ne_zero 4 hτ)]
  have h1ab : v (1 - a * b) ≤ τ := by
    have hrw : 1 - a * b = (1 - a) + a * (1 - b) := by ring
    rw [hrw]
    exact le_trans (v.map_add _ _) (max_le (le_of_eq h1a)
      (by rw [map_mul, hva, one_mul, h1b]))
  exact mul_le_mul_right h1ab _

private lemma resummation_error_lt_one {n : ℕ} {β : F} (hβ : v β = 1)
    (z r : ℕ → F) (h240 : v (240 : F) ≤ 1) (h1440 : v (1440 : F) ≤ 1)
    (h2880 : v (2880 : F) ≤ 1)
    (hr : ∀ k ∈ Finset.Icc 1 n, v (r k) < 1)
    (hzr : ∀ k ∈ Finset.Icc 1 n, v (z k) * v (r k) < 1) :
    v (240 * β * ∑ k ∈ Finset.Icc 1 n, r k
        + 2880 * β * ∑ k ∈ Finset.Icc 1 n, z k * r k
        + 1440 * ∑ k ∈ Finset.Icc 1 n, r k ^ 2) < 1 := by
  have h1 : v (240 * β * ∑ k ∈ Finset.Icc 1 n, r k) < 1 := by
    rw [map_mul, map_mul, hβ, mul_one]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' h240)
      (v.map_sum_lt one_ne_zero hr)
  have h2 : v (2880 * β * ∑ k ∈ Finset.Icc 1 n, z k * r k) < 1 := by
    rw [map_mul, map_mul, hβ, mul_one]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h2880)
      (v.map_sum_lt one_ne_zero fun k hk => ?_)
    rw [map_mul]; exact hzr k hk
  have h3 : v (1440 * ∑ k ∈ Finset.Icc 1 n, r k ^ 2) < 1 := by
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' h1440)
      (v.map_sum_lt one_ne_zero fun k hk => ?_)
    rw [map_pow, sq]
    calc v (r k) * v (r k) ≤ 1 * v (r k) := mul_le_mul_left (hr k hk).le _
      _ = v (r k) := one_mul _
      _ < 1 := hr k hk
  calc v _ ≤ max (max (v _) (v _)) (v _) :=
        le_trans (v.map_add _ _) (max_le_max (v.map_add _ _) le_rfl)
    _ < 1 := max_lt (max_lt h1 h2) h3

private lemma one_add_zsum_rw {n : ℕ} (z : ℕ → F) :
    1 + 240 * ∑ k ∈ Finset.Icc 1 n, z k + 1440 * ∑ k ∈ Finset.Icc 1 n, z k ^ 2
      = 1 + 240 * ∑ k ∈ Finset.Icc 1 n, (z k + 6 * z k ^ 2) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

private lemma centred_split {n : ℕ} (β : F) (X z r : ℕ → F)
    (hX : ∀ k ∈ Finset.Icc 1 n, X k = β * z k + r k) :
    β ^ 2 + 240 * β * (∑ k ∈ Finset.Icc 1 n, X k) + 1440 * ∑ k ∈ Finset.Icc 1 n, X k ^ 2
      = β ^ 2 * (1 + 240 * ∑ k ∈ Finset.Icc 1 n, z k + 1440 * ∑ k ∈ Finset.Icc 1 n, z k ^ 2)
        + (240 * β * ∑ k ∈ Finset.Icc 1 n, r k
          + 2880 * β * ∑ k ∈ Finset.Icc 1 n, z k * r k
          + 1440 * ∑ k ∈ Finset.Icc 1 n, r k ^ 2) := by
  have hXsum : ∑ k ∈ Finset.Icc 1 n, X k
      = β * ∑ k ∈ Finset.Icc 1 n, z k + ∑ k ∈ Finset.Icc 1 n, r k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk => hX k hk
  have hXsqsum : ∑ k ∈ Finset.Icc 1 n, X k ^ 2
      = β ^ 2 * ∑ k ∈ Finset.Icc 1 n, z k ^ 2
        + 2 * β * ∑ k ∈ Finset.Icc 1 n, z k * r k + ∑ k ∈ Finset.Icc 1 n, r k ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk => by rw [hX k hk]; ring
  rw [hXsum, hXsqsum]; ring

end Resummation

section ResummationFinal

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

private theorem resummation_final {n p : ℕ} {β : F} (hβ : v β = 1)
    (hvp : v (p : F) < 1)
    (X z : ℕ → F) (h240 : v (240 : F) ≤ 1) (h1440 : v (1440 : F) ≤ 1)
    (h2880 : v (2880 : F) ≤ 1)
    (hr : ∀ k ∈ Finset.Icc 1 n, v (X k - β * z k) < 1)
    (hzr : ∀ k ∈ Finset.Icc 1 n, v (z k) * v (X k - β * z k) < 1)
    (hpsums : 1 + 240 * ∑ k ∈ Finset.Icc 1 n, z k
        + 1440 * ∑ k ∈ Finset.Icc 1 n, z k ^ 2 = (p : F) ^ 4) :
    v (β ^ 2 + 240 * β * (∑ k ∈ Finset.Icc 1 n, X k)
        + 1440 * ∑ k ∈ Finset.Icc 1 n, X k ^ 2) < 1 := by
  set r : ℕ → F := fun k => X k - β * z k with hrdef
  have hX : ∀ k ∈ Finset.Icc 1 n, X k = β * z k + r k := fun k _ => by
    simp only [r]; ring
  rw [centred_split β X z r hX, hpsums]
  refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
  · rw [map_mul, map_pow, map_pow, hβ, one_pow, one_mul]
    exact pow_lt_one₀ zero_le' hvp (by omega)
  · exact resummation_error_lt_one v hβ z r h240 h1440 h2880 hr hzr

private lemma valuation_abscissa_eq {ζ : F} {k : ℕ} {τ : Γ₀} (hτ : τ ≠ 0)
    (hvζ : v (ζ ^ k) = 1) (h1ζ : v (1 - ζ ^ k) = τ) :
    v (ζ ^ k / (1 - ζ ^ k) ^ 2) * τ ^ 2 = 1 := by
  rw [map_div₀, hvζ, map_pow, h1ζ, div_mul_cancel₀ _ (pow_ne_zero 2 hτ)]

private theorem r_bound {n : ℕ} (X : ℕ → F) {β ε w ζ : F}
    (hβ : v β = 1) (hε : v ε ≤ 1) (hvw : v w = 1) (hvζ : v ζ = 1)
    {τ : Γ₀} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hwk : ∀ k ∈ Finset.Icc 1 n, v (w ^ k - 1) = τ)
    (hζk : ∀ k ∈ Finset.Icc 1 n, v (1 - ζ ^ k) = τ)
    (horb : ∀ k ∈ Finset.Icc 1 n, v (X k - β * w ^ k / (w ^ k - 1) ^ 2) ≤ v ε * τ ^ 4)
    (hwζ : v (w - ζ) ≤ τ ^ 7)
    (hwζpow : ∀ k ∈ Finset.Icc 1 n, v (w ^ k - ζ ^ k) ≤ v (w - ζ)) :
    (∀ k ∈ Finset.Icc 1 n, v (X k - β * (ζ ^ k / (1 - ζ ^ k) ^ 2)) < 1) ∧
    (∀ k ∈ Finset.Icc 1 n,
      v (ζ ^ k / (1 - ζ ^ k) ^ 2) * v (X k - β * (ζ ^ k / (1 - ζ ^ k) ^ 2)) < 1) := by
  have hτ : τ ≠ 0 := hτ0.ne'
  have hτ4 : (τ : Γ₀) ^ 4 ≠ 0 := pow_ne_zero 4 hτ
  have _ := hvw

  have hmaster : ∀ k ∈ Finset.Icc 1 n,
      v (X k - β * (ζ ^ k / (1 - ζ ^ k) ^ 2)) ≤ τ ^ 4 := by
    intro k hk
    have hwk1 : v (w ^ k - 1) = τ := hwk k hk
    have hζk1 : v (1 - ζ ^ k) = τ := hζk k hk
    have hwkne : w ^ k ≠ 1 := fun h => hτ (by rw [← hwk1, h, sub_self, Valuation.map_zero])
    have hζkne : ζ ^ k ≠ 1 := fun h => hτ (by rw [← hζk1, h, sub_self, Valuation.map_zero])
    have h1wk : v (1 - w ^ k) = τ := by
      rw [show (1 : F) - w ^ k = -(w ^ k - 1) by ring, Valuation.map_neg, hwk1]

    have hsplit : X k - β * (ζ ^ k / (1 - ζ ^ k) ^ 2)
        = (X k - β * w ^ k / (w ^ k - 1) ^ 2)
          + β * (w ^ k / (1 - w ^ k) ^ 2 - ζ ^ k / (1 - ζ ^ k) ^ 2) := by
      have hsq : (w ^ k - 1) ^ 2 = (1 - w ^ k) ^ 2 := by ring
      rw [hsq]; ring
    rw [hsplit]
    refine le_trans (v.map_add _ _) (max_le ?_ ?_)
    · calc v (X k - β * w ^ k / (w ^ k - 1) ^ 2) ≤ v ε * τ ^ 4 := horb k hk
        _ ≤ 1 * τ ^ 4 := mul_le_mul_left hε _
        _ = τ ^ 4 := one_mul _
    · rw [map_mul, hβ, one_mul]

      have habs := valuation_abscissa_sub_le v hwkne hζkne hτ
        (by rw [map_pow, hvw, one_pow]) h1wk hζk1
      have hchain : v (w ^ k / (1 - w ^ k) ^ 2 - ζ ^ k / (1 - ζ ^ k) ^ 2) * τ ^ 4
          ≤ τ ^ 4 * τ ^ 4 := by
        refine le_trans habs ?_
        calc v (w ^ k - ζ ^ k) * τ ≤ v (w - ζ) * τ :=
              mul_le_mul_left (hwζpow k hk) _
          _ ≤ τ ^ 7 * τ := mul_le_mul_left hwζ _
          _ = τ ^ 4 * τ ^ 4 := by rw [← pow_succ, ← pow_add]
      exact le_of_mul_le_mul_right hchain (lt_of_le_of_ne zero_le' (Ne.symm hτ4))
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · exact lt_of_le_of_lt (hmaster k hk) (pow_lt_one₀ zero_le' hτ1 (by omega))
  · have hvzk : v (ζ ^ k / (1 - ζ ^ k) ^ 2) * τ ^ 2 = 1 :=
      valuation_abscissa_eq v hτ (by rw [map_pow, hvζ, one_pow]) (hζk k hk)
    calc v (ζ ^ k / (1 - ζ ^ k) ^ 2) * v (X k - β * (ζ ^ k / (1 - ζ ^ k) ^ 2))
        ≤ v (ζ ^ k / (1 - ζ ^ k) ^ 2) * τ ^ 4 := mul_le_mul_right (hmaster k hk) _
      _ = (v (ζ ^ k / (1 - ζ ^ k) ^ 2) * τ ^ 2) * τ ^ 2 := by rw [mul_assoc, ← pow_add]
      _ = τ ^ 2 := by rw [hvzk, one_mul]
      _ < 1 := pow_lt_one₀ zero_le' hτ1 (by omega)

end ResummationFinal

section FormalCheb

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

private lemma fc4n_c_sub_c_one {w : F} (hw0 : w ≠ 0) (j : ℕ) :
    (w ^ (j + 1) - 1) ^ 2 / w ^ (j + 1) - (w - 1) ^ 2 / w
      = (w ^ (j + 1 + 1) - 1) * (w ^ j - 1) / w ^ (j + 1) := by
  rw [div_sub_div _ _ (pow_ne_zero _ hw0) hw0, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hw0) hw0)
    (pow_ne_zero _ hw0)]
  ring

private lemma fc4n_c_rec {w : F} (hw0 : w ≠ 0) (j : ℕ) :
    ((w ^ (j + 1) - 1) ^ 2 / w ^ (j + 1) - (w - 1) ^ 2 / w) ^ 2
      = (w ^ (j + 1 + 1) - 1) ^ 2 / w ^ (j + 1 + 1) * ((w ^ j - 1) ^ 2 / w ^ j) := by
  rw [fc4n_c_sub_c_one hw0 j]
  rw [div_pow, div_mul_div_comm, div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hw0))
    (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hw0))]
  ring

private lemma fc4n_c_two {w : F} (hw0 : w ≠ 0) :
    (w ^ 2 - 1) ^ 2 / w ^ 2 = ((w - 1) ^ 2 / w) ^ 2 + 4 * ((w - 1) ^ 2 / w) := by
  field_simp
  ring

private lemma fc4n_Y_eq_c_one {Y w : F} (hw : w ^ 2 - (2 + Y) * w + 1 = 0) (hw0 : w ≠ 0) :
    Y = (w - 1) ^ 2 / w := by
  rw [eq_div_iff hw0]
  linear_combination (-1 : F) * hw

private lemma fc4n_w_ne_zero {Y w : F} (hw : w ^ 2 - (2 + Y) * w + 1 = 0) : w ≠ 0 := by
  rintro rfl
  norm_num at hw

private lemma fc4n_v_w {Y w : F} (hw : w ^ 2 - (2 + Y) * w + 1 = 0) (hY : v Y < 1)
    (h2 : v (2 : F) = 1) : v w = 1 := by
  have hprod : v w * v ((2 + Y) - w) = 1 := by
    rw [← map_mul, show w * ((2 + Y) - w) = 1 by linear_combination (-1 : F) * hw, map_one]
  have h2Y : v (2 + Y) = 1 := by rw [Valuation.map_add_eq_of_lt_left _ (by rwa [h2]), h2]
  rcases lt_trichotomy (v w) 1 with hlt | heq | hgt
  · exfalso
    have : v ((2 + Y) - w) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_left _ (by rwa [h2Y]), h2Y]
    rw [this, mul_one] at hprod
    exact hlt.ne hprod
  · exact heq
  · exfalso
    have : v ((2 + Y) - w) = v w := by
      rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ (by rwa [h2Y])]
    rw [this] at hprod
    have h1 : (1 : Γ₀) < v w * v w := by
      calc (1 : Γ₀) = 1 * 1 := (mul_one _).symm
        _ < v w * v w := mul_lt_mul'' hgt hgt zero_le' zero_le'
    exact h1.ne' hprod

private lemma fc4n_v_sub_one_sq {Y w : F} (hw : w ^ 2 - (2 + Y) * w + 1 = 0) (hvw : v w = 1) :
    v (w - 1) ^ 2 = v Y := by
  have : (w - 1) ^ 2 = Y * w := by linear_combination hw
  rw [← map_pow, this, map_mul, hvw, mul_one]

private lemma fc4n_v_sub_one_lt {Y w : F} (hw : w ^ 2 - (2 + Y) * w + 1 = 0) (hvw : v w = 1)
    (hY : v Y < 1) : v (w - 1) < 1 := by
  by_contra h
  push Not at h
  have h2 : (1 : Γ₀) ≤ v (w - 1) ^ 2 := by
    calc (1 : Γ₀) = 1 * 1 := (mul_one _).symm
      _ ≤ v (w - 1) * v (w - 1) := mul_le_mul' h h
      _ = v (w - 1) ^ 2 := (sq _).symm
  rw [fc4n_v_sub_one_sq v hw hvw] at h2
  exact absurd hY (not_lt.mpr h2)

private lemma fc4n_v_geom_sum {w : F} (hvw : v w = 1) (ht : v (w - 1) < 1)
    {p : ℕ} (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) :
    v (∑ i ∈ Finset.range j, w ^ i) = 1 := by
  have hsmall : v (∑ i ∈ Finset.range j, (w ^ i - 1)) < 1 := by
    refine Valuation.map_sum_lt v one_ne_zero fun i _ => ?_
    rw [← geom_sum_mul, map_mul]
    calc v (∑ k ∈ Finset.range i, w ^ k) * v (w - 1)
        ≤ 1 * v (w - 1) := by
          refine mul_le_mul' (Valuation.map_sum_le v fun k _ => ?_) le_rfl
          rw [map_pow, hvw, one_pow]
      _ < 1 := by rw [one_mul]; exact ht
  have hsplit : ∑ i ∈ Finset.range j, w ^ i = (j : F) + ∑ i ∈ Finset.range j, (w ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rwa [hv j hj1 hjp]), hv j hj1 hjp]

private lemma fc4n_v_pow_sub_one {w : F} (hvw : v w = 1) (ht : v (w - 1) < 1)
    {p : ℕ} (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) :
    v (w ^ j - 1) = v (w - 1) := by
  rw [← geom_sum_mul, map_mul, fc4n_v_geom_sum v hvw ht hv hj1 hjp, one_mul]

private lemma fc4n_v_c {w : F} (hvw : v w = 1) (ht : v (w - 1) < 1)
    {p : ℕ} (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) :
    v ((w ^ j - 1) ^ 2 / w ^ j) = v (w - 1) ^ 2 := by
  rw [map_div₀, map_pow, map_pow, hvw, one_pow, div_one, fc4n_v_pow_sub_one v hvw ht hv hj1 hjp]

private lemma fc4n_v_c_sub {w : F} (hw0 : w ≠ 0) (hvw : v w = 1) (ht : v (w - 1) < 1)
    {p : ℕ} (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j + 1 + 1 < p) :
    v ((w ^ (j + 1) - 1) ^ 2 / w ^ (j + 1) - (w - 1) ^ 2 / w) = v (w - 1) ^ 2 := by
  rw [fc4n_c_sub_c_one hw0, map_div₀, map_mul, map_pow, hvw, one_pow, div_one,
    fc4n_v_pow_sub_one v hvw ht hv (by omega) hjp, fc4n_v_pow_sub_one v hvw ht hv hj1 (by omega), sq]

private lemma fc4n_v_natCast_le (n : ℕ) : v (n : F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by rw [map_one])

private lemma fc4n_v_of_near {Y c : F} {t E : Γ₀} (hc : v c = t) (he : v (Y - c) ≤ E)
    (hE : E < t) : v Y = t := by
  have : Y = c + (Y - c) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt he (hE.trans_eq hc.symm)), hc]

private lemma fc4n_E_lt {ε : F} {t : Γ₀} (hε : v ε ≤ 1) (ht0 : 0 < t) (ht1 : t < 1) :
    v ε * t ^ 8 < t ^ 2 :=
  calc v ε * t ^ 8 ≤ 1 * t ^ 8 := mul_le_mul' hε le_rfl
    _ = t ^ 8 := one_mul _
    _ < t ^ 2 := pow_lt_pow_right_of_lt_one₀ ht0 ht1 (by norm_num)

private lemma fc4n_ne_zero_of_v_eq_one {x : F} (hx : v x = 1) : x ≠ 0 := by
  rintro rfl
  rw [Valuation.map_zero] at hx
  exact zero_ne_one hx

private theorem fc4n_step_two {X1 X2 β ε c1 : F} {t : Γ₀}
    (hβ : v β = 1) (hε : v ε ≤ 1) (ht1 : t < 1)
    (hX1 : X1 ≠ 0) (hY1 : β / X1 = c1) (hvc1 : v c1 = t ^ 2)
    (hD : X2 * (4 * X1 ^ 3 + β * X1 ^ 2 - 4 * ε) = X1 ^ 4 + 8 * ε * X1 + β * ε) :
    X2 ≠ 0 ∧ v (β / X2 - (c1 ^ 2 + 4 * c1)) ≤ v ε * t ^ 8 := by
  have hβ0 : β ≠ 0 := fc4n_ne_zero_of_v_eq_one v hβ
  obtain ⟨η, hη⟩ : ∃ η, η = ε / β ^ 3 := ⟨_, rfl⟩
  have hvη : v η = v ε := by rw [hη, map_div₀, map_pow, hβ, one_pow, div_one]
  have hvY1 : v (β / X1) = t ^ 2 := by rw [hY1, hvc1]
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ zero_le' ht1.le

  have hvδ : v (η * (β / X1) ^ 3 * (8 + β / X1)) ≤ v ε * t ^ 6 := by
    rw [map_mul, map_mul, map_pow, hvη, hvY1, ← pow_mul]
    refine mul_le_of_le_one_right' (Valuation.map_add_le _ (fc4n_v_natCast_le v 8) ?_)
    rw [hvY1]; exact ht2
  have hvδ1 : v (η * (β / X1) ^ 3 * (8 + β / X1)) < 1 := by
    refine lt_of_le_of_lt hvδ ?_
    calc v ε * t ^ 6 ≤ 1 * t ^ 6 := mul_le_mul' hε le_rfl
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' ht1 (by norm_num)
  have hvDn : v (1 + η * (β / X1) ^ 3 * (8 + β / X1)) = 1 := by
    rw [mul_assoc]; rw [mul_assoc] at hvδ1
    exact Valuation.map_one_add_of_lt _ hvδ1
  have hDn0 : 1 + η * (β / X1) ^ 3 * (8 + β / X1) ≠ 0 := fc4n_ne_zero_of_v_eq_one v hvDn

  have hRHS : X1 ^ 4 + 8 * ε * X1 + β * ε = X1 ^ 4 * (1 + η * (β / X1) ^ 3 * (8 + β / X1)) := by
    rw [hη]; field_simp; ring
  have hX2 : X2 ≠ 0 := by
    rintro rfl
    rw [zero_mul, hRHS] at hD
    exact mul_ne_zero (pow_ne_zero 4 hX1) hDn0 hD.symm
  refine ⟨hX2, ?_⟩

  have hfac : 1 + η * (β / X1) ^ 3 * (8 + β / X1)
      = X2 * (4 * X1 ^ 3 + β * X1 ^ 2 - 4 * ε) / X1 ^ 4 := by
    rw [hD, hRHS, mul_div_cancel_left₀ _ (pow_ne_zero 4 hX1)]
  have key : (β / X2) * (1 + η * (β / X1) ^ 3 * (8 + β / X1))
      = (β / X1) ^ 2 + 4 * (β / X1) - 4 * η * (β / X1) ^ 4 := by
    rw [hfac, hη]; field_simp; ring

  have hid : (β / X2 - (c1 ^ 2 + 4 * c1)) * (1 + η * (β / X1) ^ 3 * (8 + β / X1))
      = -(η * c1 ^ 4 * (c1 + 6) ^ 2) := by
    rw [hY1] at key ⊢
    linear_combination key

  have hL : v ((β / X2 - (c1 ^ 2 + 4 * c1)) * (1 + η * (β / X1) ^ 3 * (8 + β / X1)))
      = v (β / X2 - (c1 ^ 2 + 4 * c1)) := by
    rw [map_mul, hvDn, mul_one]
  have hR : v (-(η * c1 ^ 4 * (c1 + 6) ^ 2)) ≤ v ε * t ^ 8 := by
    rw [Valuation.map_neg, map_mul, map_mul, map_pow, hvη, hvc1, ← pow_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_pow]
    exact pow_le_one₀ zero_le' (Valuation.map_add_le _ (hvc1.le.trans ht2) (fc4n_v_natCast_le v 6))
  rw [← hL, hid]
  exact hR

private theorem fc4n_step {X1 Xm Xmm Xp β ε c1 cm cmm cp : F} {t : Γ₀}
    (hβ : v β = 1) (hε : v ε ≤ 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hX1 : X1 ≠ 0) (hXm : Xm ≠ 0) (hXmm : Xmm ≠ 0)
    (hY1 : β / X1 = c1) (hvc1 : v c1 = t ^ 2) (hvcm : v cm = t ^ 2) (hvcmm : v cmm = t ^ 2)
    (hvcsub : v (cm - c1) = t ^ 2) (hcheb : (cm - c1) ^ 2 = cp * cmm)
    (hem : v (β / Xm - cm) ≤ v ε * t ^ 8) (hemm : v (β / Xmm - cmm) ≤ v ε * t ^ 8)
    (hR : Xp * Xmm * (Xm - X1) ^ 2 = (Xm * X1) ^ 2 + ε * (4 * Xm + 4 * X1 + β)) :
    Xp ≠ 0 ∧ v (β / Xp - cp) ≤ v ε * t ^ 8 := by
  have hβ0 : β ≠ 0 := fc4n_ne_zero_of_v_eq_one v hβ
  have hE : v ε * t ^ 8 < t ^ 2 := fc4n_E_lt v hε ht0 ht1
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ zero_le' ht1.le
  have hvYm : v (β / Xm) = t ^ 2 := fc4n_v_of_near v hvcm hem hE
  have hvYmm : v (β / Xmm) = t ^ 2 := fc4n_v_of_near v hvcmm hemm hE
  have hvY1 : v (β / X1) = t ^ 2 := by rw [hY1, hvc1]
  obtain ⟨η, hη⟩ : ∃ η, η = ε / β ^ 3 := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (β / Xm) * (β / X1)
      * (4 * (β / X1) + 4 * (β / Xm) + (β / Xm) * (β / X1)) := ⟨_, rfl⟩
  have hvη : v η = v ε := by rw [hη, map_div₀, map_pow, hβ, one_pow, div_one]
  have h4 : v (4 : F) ≤ 1 := fc4n_v_natCast_le v 4
  have hvρ : v ρ ≤ t ^ 2 * t ^ 2 * t ^ 2 := by
    rw [hρ, map_mul, map_mul, hvYm, hvY1]
    refine mul_le_mul' le_rfl (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_)
    · rw [map_mul, hvY1]; exact mul_le_of_le_one_left' h4
    · rw [map_mul, hvYm]; exact mul_le_of_le_one_left' h4
    · rw [map_mul, hvYm, hvY1]; exact mul_le_of_le_one_left' ht2
  have hvηρ : v (η * ρ) ≤ v ε * (t ^ 2 * t ^ 2 * t ^ 2) := by
    rw [map_mul, hvη]; exact mul_le_mul' le_rfl hvρ
  have hvηρ1 : v (η * ρ) < 1 := by
    refine lt_of_le_of_lt hvηρ ?_
    calc v ε * (t ^ 2 * t ^ 2 * t ^ 2) ≤ 1 * (t ^ 2 * t ^ 2 * 1) :=
          mul_le_mul' hε (mul_le_mul' le_rfl ht2)
      _ < 1 := by
          rw [one_mul, mul_one, ← pow_add]
          exact pow_lt_one₀ zero_le' ht1 (by norm_num)
  have hvD : v (1 + η * ρ) = 1 := Valuation.map_one_add_of_lt _ hvηρ1
  have hD0 : 1 + η * ρ ≠ 0 := fc4n_ne_zero_of_v_eq_one v hvD

  have hRHS : (Xm * X1) ^ 2 + ε * (4 * Xm + 4 * X1 + β) = (Xm * X1) ^ 2 * (1 + η * ρ) := by
    rw [hη, hρ]; field_simp
  have hXp : Xp ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul, hRHS] at hR
    exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero hXm hX1)) hD0 hR.symm
  refine ⟨hXp, ?_⟩

  have hfac : 1 + η * ρ = Xp * Xmm * (Xm - X1) ^ 2 / (Xm * X1) ^ 2 := by
    rw [hR, hRHS, mul_div_cancel_left₀ _ (pow_ne_zero 2 (mul_ne_zero hXm hX1))]
  have key : (β / Xm - c1) ^ 2 = (β / Xp) * (β / Xmm) * (1 + η * ρ) := by
    rw [hfac, ← hY1]; field_simp; ring

  have hid : (β / Xp - cp) * (cmm * (β / Xmm) * (1 + η * ρ))
      = cmm * (2 * (cm - c1) * (β / Xm - cm) + (β / Xm - cm) ^ 2)
        - (cm - c1) ^ 2 * ((β / Xmm - cmm) + η * ρ * (β / Xmm)) := by
    linear_combination (-cmm) * key + ((β / Xmm) * (1 + η * ρ)) * hcheb

  have hL : v ((β / Xp - cp) * (cmm * (β / Xmm) * (1 + η * ρ)))
      = v (β / Xp - cp) * (t ^ 2 * t ^ 2) := by
    rw [map_mul, map_mul, map_mul, hvcmm, hvYmm, hvD, mul_one]

  have hA : v (cmm * (2 * (cm - c1) * (β / Xm - cm) + (β / Xm - cm) ^ 2))
      ≤ t ^ 2 * (t ^ 2 * (v ε * t ^ 8)) := by
    rw [map_mul, hvcmm]
    refine mul_le_mul' le_rfl (Valuation.map_add_le _ ?_ ?_)
    · rw [map_mul, map_mul, hvcsub]
      calc v (2 : F) * t ^ 2 * v (β / Xm - cm) ≤ 1 * t ^ 2 * (v ε * t ^ 8) :=
            mul_le_mul' (mul_le_mul' (fc4n_v_natCast_le v 2) le_rfl) hem
        _ = t ^ 2 * (v ε * t ^ 8) := by rw [one_mul]
    · rw [map_pow, sq]
      exact mul_le_mul' (hem.trans hE.le) hem
  have hB : v ((cm - c1) ^ 2 * ((β / Xmm - cmm) + η * ρ * (β / Xmm)))
      ≤ (t ^ 2 * t ^ 2) * (v ε * t ^ 8) := by
    rw [map_mul, map_pow, hvcsub, sq]
    refine mul_le_mul' le_rfl (Valuation.map_add_le _ hemm ?_)
    rw [map_mul, hvYmm]
    calc v (η * ρ) * t ^ 2 ≤ v ε * (t ^ 2 * t ^ 2 * t ^ 2) * t ^ 2 := mul_le_mul' hvηρ le_rfl
      _ = v ε * t ^ 8 := by rw [mul_assoc, ← pow_add, ← pow_add, ← pow_add]
  have hRv : v (cmm * (2 * (cm - c1) * (β / Xm - cm) + (β / Xm - cm) ^ 2)
        - (cm - c1) ^ 2 * ((β / Xmm - cmm) + η * ρ * (β / Xmm)))
      ≤ (v ε * t ^ 8) * (t ^ 2 * t ^ 2) := by
    refine Valuation.map_sub_le _ (hA.trans (le_of_eq ?_)) (hB.trans (le_of_eq (mul_comm _ _)))
    ac_rfl

  have hpos : (0 : Γ₀) < t ^ 2 * t ^ 2 := mul_pos (pow_pos ht0 2) (pow_pos ht0 2)
  have := hRv
  rw [← hid, hL] at this
  exact (mul_le_mul_iff_left₀ hpos).mp this

private theorem fc4n_formal_orbit {p : ℕ} (hp3 : 3 ≤ p) (X : ℕ → F) {β ε w : F}
    (hβ : v β = 1) (hε : v ε ≤ 1) (hX1 : 1 < v (X 1))
    (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    (hD : X 2 * (4 * X 1 ^ 3 + β * X 1 ^ 2 - 4 * ε) = X 1 ^ 4 + 8 * ε * X 1 + β * ε)
    (hR : ∀ m, 2 ≤ m → m ≤ p - 2 →
      X (m + 1) * X (m - 1) * (X m - X 1) ^ 2 = (X m * X 1) ^ 2 + ε * (4 * X m + 4 * X 1 + β))
    (hw : w ^ 2 - (2 + β / X 1) * w + 1 = 0) :
    v w = 1 ∧ 0 < v (w - 1) ∧ v (w - 1) < 1 ∧
    (∀ j, 1 ≤ j → j < p → v (w ^ j - 1) = v (w - 1)) ∧
    ∀ m, 1 ≤ m → m ≤ p - 1 →
      X m ≠ 0 ∧ v (β / X m - (w ^ m - 1) ^ 2 / w ^ m) ≤ v ε * v (w - 1) ^ 8 := by

  have hX10 : X 1 ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hX1
    exact lt_irrefl (0 : Γ₀) (lt_of_le_of_lt zero_le' hX1)
  have hvY1 : v (β / X 1) < 1 := by
    rw [map_div₀, div_lt_one₀ (lt_of_le_of_lt zero_le' hX1), hβ]; exact hX1
  have h2 : v (2 : F) = 1 := by
    have := hv 2 (by norm_num) (by omega)
    simpa using this
  have hw0 : w ≠ 0 := fc4n_w_ne_zero hw
  have hvw : v w = 1 := fc4n_v_w v hw hvY1 h2
  have ht1 : v (w - 1) < 1 := fc4n_v_sub_one_lt v hw hvw hvY1
  have hY1 : β / X 1 = (w - 1) ^ 2 / w := fc4n_Y_eq_c_one hw hw0
  have hvc1 : v ((w - 1) ^ 2 / w) = v (w - 1) ^ 2 := by
    rw [map_div₀, map_pow, hvw, div_one]
  have ht0 : 0 < v (w - 1) := by
    rw [zero_lt_iff]
    intro h0
    have : v (β / X 1) = 0 := by rw [hY1, hvc1, h0, zero_pow two_ne_zero]
    rw [map_div₀, hβ, div_eq_zero_iff] at this
    rcases this with h | h
    · exact one_ne_zero h
    · exact hX10 ((Valuation.zero_iff v).mp h)
  have hvpow : ∀ j, 1 ≤ j → j < p → v (w ^ j - 1) = v (w - 1) :=
    fun j hj1 hjp => fc4n_v_pow_sub_one v hvw ht1 hv hj1 hjp
  have hvc : ∀ j, 1 ≤ j → j < p → v ((w ^ j - 1) ^ 2 / w ^ j) = v (w - 1) ^ 2 :=
    fun j hj1 hjp => fc4n_v_c v hvw ht1 hv hj1 hjp
  refine ⟨hvw, ht0, ht1, hvpow, ?_⟩

  have P1 : X 1 ≠ 0 ∧ v (β / X 1 - (w ^ 1 - 1) ^ 2 / w ^ 1) ≤ v ε * v (w - 1) ^ 8 := by
    refine ⟨hX10, ?_⟩
    simp only [pow_one]
    rw [hY1, sub_self, Valuation.map_zero]
    exact zero_le'
  have P2 : X 2 ≠ 0 ∧ v (β / X 2 - (w ^ 2 - 1) ^ 2 / w ^ 2) ≤ v ε * v (w - 1) ^ 8 := by
    rw [fc4n_c_two hw0]
    exact fc4n_step_two v hβ hε ht1 hX10 hY1 hvc1 hD

  have key : ∀ m, 1 ≤ m → m + 1 ≤ p - 1 →
      (X m ≠ 0 ∧ v (β / X m - (w ^ m - 1) ^ 2 / w ^ m) ≤ v ε * v (w - 1) ^ 8) ∧
      (X (m + 1) ≠ 0 ∧
        v (β / X (m + 1) - (w ^ (m + 1) - 1) ^ 2 / w ^ (m + 1)) ≤ v ε * v (w - 1) ^ 8) := by
    intro m hm1 hmp
    induction m with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact ⟨P1, P2⟩
      · obtain ⟨⟨hXj, hej⟩, ⟨hXj1, hej1⟩⟩ := ih hj (by omega)
        refine ⟨⟨hXj1, hej1⟩, ?_⟩
        have hRj := hR (j + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at hRj
        exact fc4n_step v hβ hε ht0 ht1 hX10 hXj1 hXj hY1 hvc1 (hvc (j + 1) (by omega) (by omega))
          (hvc j hj (by omega)) (fc4n_v_c_sub v hw0 hvw ht1 hv hj (by omega)) (fc4n_c_rec hw0 j)
          hej1 hej hRj
  intro m hm1 hmp
  rcases lt_or_eq_of_le hmp with hlt | heq
  · exact (key m hm1 (by omega)).1
  · have := (key (m - 1) (by omega) (by omega)).2
    rwa [show m - 1 + 1 = m by omega] at this

private theorem fc4n_formal_closure {p : ℕ} (hp3 : 3 ≤ p) (X : ℕ → F) {β ε w : F}
    (hβ : v β = 1) (hε : v ε ≤ 1) (hX1 : 1 < v (X 1))
    (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    (hD : X 2 * (4 * X 1 ^ 3 + β * X 1 ^ 2 - 4 * ε) = X 1 ^ 4 + 8 * ε * X 1 + β * ε)
    (hR : ∀ m, 2 ≤ m → m ≤ p - 2 →
      X (m + 1) * X (m - 1) * (X m - X 1) ^ 2 = (X m * X 1) ^ 2 + ε * (4 * X m + 4 * X 1 + β))
    (hw : w ^ 2 - (2 + β / X 1) * w + 1 = 0) (hS : X (p - 1) = X 1) :
    v (w ^ p - 1) ≤ v ε * v (w - 1) ^ 7 := by
  obtain ⟨hvw, ht0, -, hvpow, horb⟩ := fc4n_formal_orbit v hp3 X hβ hε hX1 hv hD hR hw
  have hw0 : w ≠ 0 := fc4n_w_ne_zero hw
  obtain ⟨-, hlast⟩ := horb (p - 1) (by omega) le_rfl
  obtain ⟨j, hj⟩ : ∃ j, p - 1 = j + 1 := ⟨p - 2, by omega⟩
  rw [hS, fc4n_Y_eq_c_one hw hw0, hj, Valuation.map_sub_swap, fc4n_c_sub_c_one hw0 j,
    show j + 1 + 1 = p by omega, map_div₀, map_mul, map_pow, hvw, one_pow, div_one,
    hvpow j (by omega) (by omega)] at hlast
  rw [show v ε * v (w - 1) ^ 8 = v ε * v (w - 1) ^ 7 * v (w - 1) by rw [mul_assoc, ← pow_succ]]
    at hlast
  exact (mul_le_mul_iff_left₀ ht0).mp hlast

private lemma fc4n_track_X {X β c ε : F} {t : Γ₀} (hβ : v β = 1) (hε : v ε ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hX : X ≠ 0) (hvc : v c = t ^ 2)
    (he : v (β / X - c) ≤ v ε * t ^ 8) :
    v X * t ^ 2 = 1 ∧ v (X - β / c) ≤ v ε * t ^ 4 := by
  have hE : v ε * t ^ 8 < t ^ 2 := fc4n_E_lt v hε ht0 ht1
  have hvY : v (β / X) = t ^ 2 := fc4n_v_of_near v hvc he hE
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hvc
    exact pow_ne_zero 2 ht0.ne' hvc.symm
  have h1 : v X * t ^ 2 = 1 := by
    rw [← hvY, ← map_mul, show X * (β / X) = β by field_simp, hβ]
  refine ⟨h1, ?_⟩
  have hid : (X - β / c) * c = -(X * (β / X - c)) := by field_simp; ring
  have h2 : v (X - β / c) * t ^ 2 = v X * v (β / X - c) := by
    rw [← hvc, ← map_mul, hid, Valuation.map_neg, map_mul]
  have h3 : v (X - β / c) * (t ^ 2 * t ^ 2) ≤ v ε * t ^ 4 * (t ^ 2 * t ^ 2) := by
    calc v (X - β / c) * (t ^ 2 * t ^ 2) = v X * t ^ 2 * v (β / X - c) := by
          rw [← mul_assoc, h2]; ac_rfl
      _ = v (β / X - c) := by rw [h1, one_mul]
      _ ≤ v ε * t ^ 8 := he
      _ = v ε * t ^ 4 * (t ^ 2 * t ^ 2) := by rw [mul_assoc, ← pow_add, ← pow_add]
  exact (mul_le_mul_iff_left₀ (mul_pos (pow_pos ht0 2) (pow_pos ht0 2))).mp h3

private theorem fc4n_formal_orbit_X {p : ℕ} (hp3 : 3 ≤ p) (X : ℕ → F) {β ε w : F}
    (hβ : v β = 1) (hε : v ε ≤ 1) (hX1 : 1 < v (X 1))
    (hv : ∀ j : ℕ, 1 ≤ j → j < p → v (j : F) = 1)
    (hD : X 2 * (4 * X 1 ^ 3 + β * X 1 ^ 2 - 4 * ε) = X 1 ^ 4 + 8 * ε * X 1 + β * ε)
    (hR : ∀ m, 2 ≤ m → m ≤ p - 2 →
      X (m + 1) * X (m - 1) * (X m - X 1) ^ 2 = (X m * X 1) ^ 2 + ε * (4 * X m + 4 * X 1 + β))
    (hw : w ^ 2 - (2 + β / X 1) * w + 1 = 0) :
    v w = 1 ∧ 0 < v (w - 1) ∧ v (w - 1) < 1 ∧
    (∀ j, 1 ≤ j → j < p → v (w ^ j - 1) = v (w - 1)) ∧
    ∀ m, 1 ≤ m → m ≤ p - 1 →
      X m ≠ 0 ∧ v (X m) * v (w - 1) ^ 2 = 1 ∧
      v (X m - β * w ^ m / (w ^ m - 1) ^ 2) ≤ v ε * v (w - 1) ^ 4 := by
  obtain ⟨hvw, ht0, ht1, hvpow, horb⟩ := fc4n_formal_orbit v hp3 X hβ hε hX1 hv hD hR hw
  refine ⟨hvw, ht0, ht1, hvpow, fun m hm1 hmp => ?_⟩
  obtain ⟨hXm, hem⟩ := horb m hm1 hmp
  have hvc : v ((w ^ m - 1) ^ 2 / w ^ m) = v (w - 1) ^ 2 :=
    fc4n_v_c v hvw ht1 hv hm1 (by omega)
  obtain ⟨h1, h2⟩ := fc4n_track_X v hβ hε ht0 ht1 hXm hvc hem
  refine ⟨hXm, h1, ?_⟩
  rwa [div_div_eq_mul_div] at h2

private lemma fc4n_exists_cheb_root {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (Y : K) : ∃ w : K, w ^ 2 - (2 + Y) * w + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (Y ^ 2 + 4 * Y) two_pos
  refine ⟨((2 + Y) + s) / 2, ?_⟩
  field_simp
  linear_combination hs

end FormalCheb

end FormalC4Aux

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hQord : addOrderOf (Point.some x y h) = p) (hx : x ∉ A) :
    A.valuation ((W.c₄ : AlgebraicClosure ℚ)
      + 240 * ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluTSum
          (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet
            (Point.some x y h) (p / 2))) < 1 := by

  obtain rfl : q = p := FormalC4Aux.step0_q_eq_p W hq A hA hp h hQord hx
  have hp3 : 3 ≤ q := by have := hq.two_le; omega

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    W.exists_criticalCentre_of_multiplicativeReduction hq hΔ hqΔ hqc₄ A hA
  obtain ⟨β, hβdef⟩ : ∃ β : AlgebraicClosure ℚ, β = (W.b₂ : AlgebraicClosure ℚ) + 12 * x₀ :=
    ⟨_, rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : AlgebraicClosure ℚ, ε = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) := ⟨_, rfl⟩
  have hvβ : A.valuation β = 1 := by rw [hβdef]; exact hnode
  have hvε1 : A.valuation ε < 1 := by rw [hεdef]; exact hbad

  have hq0 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
  have hvεq : A.valuation ε ≤ A.valuation ((q : ℕ) : AlgebraicClosure ℚ) := by
    rw [hεdef, ← W.valuation_discriminant_eq_of_criticalCentre A hx₀ hy₀ hFy hFx hnode hbad]
    exact FormalC4Aux.valuation_intCast_le_of_dvd A hqΔ

  obtain ⟨xc, yc, hx1, -, hspec, hS, hD, hR⟩ :=
    FormalC4Aux.exists_kernel_dock hq hp2 hFy hFx hβdef hεdef hQord

  have hX1 : 1 < A.valuation (xc 1 - x₀) := by
    rw [hx1]
    have hxv : 1 < A.valuation x := (FormalC4Aux.not_mem_iff_one_lt_valuation A).mp hx
    have hx₀v : A.valuation x₀ ≤ 1 := (A.valuation_le_one_iff _).mpr hx₀
    rwa [Valuation.map_sub_eq_of_lt_left _ (lt_of_le_of_lt hx₀v hxv)]

  have hv : ∀ j : ℕ, 1 ≤ j → j < q → A.valuation (j : AlgebraicClosure ℚ) = 1 := by
    intro j hj1 hjq
    have hnd : ¬ (q : ℤ) ∣ (j : ℤ) := by
      intro hd
      have hd' : q ∣ j := Int.natCast_dvd_natCast.mp hd
      exact absurd (Nat.le_of_dvd (by omega) hd') (by omega)
    have := FormalC4Aux.valuation_intCast_eq_one_of_not_dvd A hq hA hnd
    simpa using this

  obtain ⟨w, hw⟩ := FormalC4Aux.fc4n_exists_cheb_root (two_ne_zero) (β / (xc 1 - x₀))

  obtain ⟨hvw, ht0, ht1, hvpow, horb⟩ := FormalC4Aux.fc4n_formal_orbit_X A.valuation hp3
    (fun m => xc m - x₀) hvβ hvε1.le hX1 hv hD hR hw
  have hclos : A.valuation (w ^ q - 1) ≤ A.valuation ε * A.valuation (w - 1) ^ 7 :=
    FormalC4Aux.fc4n_formal_closure A.valuation hp3 (fun m => xc m - x₀) hvβ hvε1.le hX1 hv
      hD hR hw (by simp only [hS])

  have hB : A.valuation (w ^ q - 1)
      < A.valuation ((q : ℕ) : AlgebraicClosure ℚ) * A.valuation (w - 1) :=
    FormalC4Aux.hB_of_closure A hclos hvεq hq0 ht0 ht1
  obtain ⟨ζ, hζprim, -, -, hexact, hcal⟩ :=
    FormalC4Aux.exists_primitiveRoot_valuation_close A hq hB
  have hwζ : A.valuation (w - ζ) ≤ A.valuation (w - 1) ^ 7 :=
    FormalC4Aux.valuation_w_sub_zeta_le A hexact hclos hvεq hq0

  have h2n : 2 * (q / 2) < q := by
    have := Nat.two_mul_div_two_add_one_of_odd (hq.odd_of_ne_two hp2); omega
  have htarget := FormalC4Aux.c₄_add_240T_eq_centred W hFy hFx hQord h2n
  dsimp only at htarget
  rw [htarget, ← hβdef]

  have hco : ∀ k ∈ Finset.Icc 1 (q / 2), (k • Point.some x y h).coordsOrZero.1 = xc k := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hm, heq⟩ := hspec k hk1 (by omega)
    rw [heq, coordsOrZero_some]
  have hsum1 : ∑ k ∈ Finset.Icc 1 (q / 2), ((k • Point.some x y h).coordsOrZero.1 - x₀)
      = ∑ k ∈ Finset.Icc 1 (q / 2), (xc k - x₀) :=
    Finset.sum_congr rfl fun k hk => by rw [hco k hk]
  have hsum2 : ∑ k ∈ Finset.Icc 1 (q / 2), ((k • Point.some x y h).coordsOrZero.1 - x₀) ^ 2
      = ∑ k ∈ Finset.Icc 1 (q / 2), (xc k - x₀) ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [hco k hk]
  rw [hsum1, hsum2]

  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 :=
    FormalC4Aux.valuation_natCast_lt_one A hA
  have hnat : ∀ n : ℕ, A.valuation ((n : ℕ) : AlgebraicClosure ℚ) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have h240 : A.valuation (240 : AlgebraicClosure ℚ) ≤ 1 := by exact_mod_cast hnat 240
  have h1440 : A.valuation (1440 : AlgebraicClosure ℚ) ≤ 1 := by exact_mod_cast hnat 1440
  have h2880 : A.valuation (2880 : AlgebraicClosure ℚ) ≤ 1 := by exact_mod_cast hnat 2880

  have hpsums : 1 + 240 * ∑ k ∈ Finset.Icc 1 (q / 2), ζ ^ k / (1 - ζ ^ k) ^ 2
      + 1440 * ∑ k ∈ Finset.Icc 1 (q / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
        = ((q : ℕ) : AlgebraicClosure ℚ) ^ 4 := by
    rw [FormalC4Aux.one_add_zsum_rw (fun k => ζ ^ k / (1 - ζ ^ k) ^ 2)]
    exact FormalC4Aux.one_add_240_zsum_eq_pow_four hq hp2 hζprim

  have hvζ : A.valuation ζ = 1 :=
    FormalC4Aux.valuation_eq_one_of_pow_eq_one A hq.pos hζprim.pow_eq_one
  have hwk : ∀ k ∈ Finset.Icc 1 (q / 2), A.valuation (w ^ k - 1) = A.valuation (w - 1) := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact hvpow k hk1 (by omega)
  have hζk : ∀ k ∈ Finset.Icc 1 (q / 2), A.valuation (1 - ζ ^ k) = A.valuation (w - 1) := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact hcal k fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  have horb' : ∀ k ∈ Finset.Icc 1 (q / 2),
      A.valuation ((xc k - x₀) - β * w ^ k / (w ^ k - 1) ^ 2)
        ≤ A.valuation ε * A.valuation (w - 1) ^ 4 := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact (horb k hk1 (by omega)).2.2
  have hwζpow : ∀ k ∈ Finset.Icc 1 (q / 2), A.valuation (w ^ k - ζ ^ k) ≤ A.valuation (w - ζ) :=
    fun k _ => FormalC4Aux.valuation_pow_sub_pow_le A hvw hvζ k
  obtain ⟨hr, hzr⟩ := FormalC4Aux.r_bound A.valuation (fun k => xc k - x₀) hvβ hvε1.le hvw hvζ
    ht0 ht1 hwk hζk horb' hwζ hwζpow
  exact FormalC4Aux.resummation_final A.valuation hvβ hvq (fun k => xc k - x₀)
    (fun k => ζ ^ k / (1 - ζ ^ k) ^ 2) h240 h1440 h2880 hr hzr hpsums

end S_WeierstrassCurve_valuation_c4_add_veluTSum_lt_one_of_formal_kernel
end P2MW
export P2MW.S_WeierstrassCurve_valuation_c4_add_veluTSum_lt_one_of_formal_kernel (solution)
