-- Prove2me | solution 1 for WeierstrassCurve.exists_integral_veluQuotient_rescale_of_galois_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b0b4f688-4bb2-5656-a53d-7ced42ad5d8e

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluY_empty"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

private lemma den_eq_prime_pow {p : ℕ} {r : ℚ}
    (h : ∀ q : ℕ, q.Prime → q ≠ p → 0 ≤ padicValRat q r) : ∃ e : ℕ, r.den = p ^ e := by
  refine ⟨r.den.factorization p, Nat.eq_pow_of_factorization_eq_single r.den_nz ?_⟩
  rw [Finsupp.eq_single_iff]
  refine ⟨fun q hq0 => ?_, rfl⟩
  simp only [Finset.mem_singleton]
  by_contra hqp
  have h0 : r.den.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq0
  have hqmem : q ∈ r.den.primeFactors := by
    rw [← Nat.support_factorization]
    exact hq0
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqden : q ∣ r.den := Nat.dvd_of_mem_primeFactors hqmem
  have hqnum : ¬ (q : ℤ) ∣ r.num := by
    intro hdvd
    have h1 : q ∣ r.num.natAbs := Int.natCast_dvd.mp hdvd
    have hred := r.reduced
    rw [Nat.coprime_iff_gcd_eq_one] at hred
    have : q ∣ 1 := hred ▸ Nat.dvd_gcd h1 hqden
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hv : padicValRat q r < 0 := by
    have h1 : padicValInt q r.num = 0 := padicValInt.eq_zero_of_not_dvd hqnum
    have h2 : 0 < padicValNat q r.den := by
      rw [← Nat.factorization_def _ hq]
      exact Nat.pos_of_ne_zero h0
    unfold padicValRat
    omega
  exact absurd (h q hq hqp) (not_le.mpr hv)

private lemma exists_int_eq_mul_pow {p : ℕ} {r : ℚ} {e m : ℕ}
    (hden : r.den = p ^ e) (hem : e ≤ m) : ∃ z : ℤ, (z : ℚ) = r * (p : ℚ) ^ m := by
  refine ⟨r.num * (p : ℤ) ^ (m - e), ?_⟩
  have hden0 : ((r.den : ℚ)) ≠ 0 := by
    exact_mod_cast r.den_nz
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) :=
    (div_eq_iff hden0).mp (Rat.num_div_den r)
  have hdenq : ((r.den : ℚ)) = (p : ℚ) ^ e := by
    rw [hden]; push_cast; rfl
  push_cast
  rw [hnum, hdenq, mul_assoc, ← pow_add, Nat.add_sub_cancel' hem]

private lemma summingSet_coords_mem
    (W : WeierstrassCurve ℤ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p) {n : ℕ} (hn : n < p) :
    ∀ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n,
      P.1 ∈ A ∧ P.2 ∈ A := by
  intro P hP
  rw [mem_oddOrderSummingSet] at hP
  obtain ⟨k, hk1, hkn, hkP⟩ := hP
  have hkQ : k • Q ≠ 0 := by
    intro h0
    have hdvd : addOrderOf Q ∣ k := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    rw [hQord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hpkQ : p • (k • Q) = 0 := by
    rw [smul_comm, ← hQord, addOrderOf_nsmul_eq_zero, smul_zero]
  have hqn : ¬ q ∣ p := fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd)
  rcases WeierstrassCurve.torsion_integral_of_not_dvd W hq A hA hqn (k • Q) hpkQ with
    h0 | ⟨x, y, hns, hsome, hx, hy⟩
  · exact absurd h0 hkQ
  · rw [← hkP, hsome]
    simpa using ⟨hx, hy⟩

private lemma quotient_coeffs_mem
    (W : WeierstrassCurve ℤ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p) {n : ℕ} (hn : n < p) :
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)).a₁ ∈ A ∧
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)).a₂ ∈ A ∧
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)).a₃ ∈ A ∧
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)).a₄ ∈ A ∧
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)).a₆ ∈ A := by
  have hcoords := summingSet_coords_mem W hp hq hqp A hA Q hQord hn
  have ha₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁
      = ((W.a₁ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have ha₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₂
      = ((W.a₂ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have ha₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃
      = ((W.a₃ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have ha₄ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₄
      = ((W.a₄ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have ha₆ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₆
      = ((W.a₆ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have hb₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₂
      = ((W.b₂ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]
  have hb₄ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).b₄
      = ((W.b₄ : ℤ) : AlgebraicClosure ℚ) := by
    simp [WeierstrassCurve.baseChange]

  have htP : ∀ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n,
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluT P.1 P.2 ∈ A := by
    intro P hP
    obtain ⟨hx, hy⟩ := hcoords P hP
    rw [veluT_eq, hb₂, hb₄]
    refine add_mem (add_mem (mul_mem ?_ (pow_mem hx 2)) (mul_mem (intCast_mem A _) hx))
      (intCast_mem A _)
    exact_mod_cast intCast_mem A (6 : ℤ)

  have hwP : ∀ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n,
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluW P.1 P.2 ∈ A := by
    intro P hP
    obtain ⟨hx, hy⟩ := hcoords P hP
    unfold WeierstrassCurve.veluW WeierstrassCurve.veluU WeierstrassCurve.veluGy
    refine add_mem (pow_mem (neg_mem (add_mem (add_mem (mul_mem ?_ hy)
      (mul_mem ?_ hx)) ?_)) 2) (mul_mem hx (htP P hP))
    · exact_mod_cast intCast_mem A (2 : ℤ)
    · rw [ha₁]; exact intCast_mem A _
    · rw [ha₃]; exact intCast_mem A _

  have ht : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluTSum
      (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n) ∈ A := by
    show (∑ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n,
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluT P.1 P.2) ∈ A
    exact sum_mem htP
  have hw : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluWSum
      (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n) ∈ A := by
    show (∑ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n,
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluW P.1 P.2) ∈ A
    exact sum_mem hwP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [veluQuotient_a₁, ha₁]; exact intCast_mem A _
  · rw [veluQuotient_a₂, ha₂]; exact intCast_mem A _
  · rw [veluQuotient_a₃, ha₃]; exact intCast_mem A _
  · rw [veluQuotient_a₄, ha₄]
    refine sub_mem (intCast_mem A _) (mul_mem ?_ ht)
    exact_mod_cast intCast_mem A (5 : ℤ)
  · rw [veluQuotient_a₆, ha₆, hb₂]
    refine sub_mem (sub_mem (intCast_mem A _) (mul_mem (intCast_mem A _) ht)) (mul_mem ?_ hw)
    exact_mod_cast intCast_mem A (7 : ℤ)

private lemma coeff_padic_nonneg
    (W : WeierstrassCurve ℤ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p) {n : ℕ} (hn : n < p)
    (V₀ : WeierstrassCurve ℚ)
    (hV₀ : V₀.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q n)) :
    0 ≤ padicValRat q V₀.a₁ ∧ 0 ≤ padicValRat q V₀.a₂ ∧ 0 ≤ padicValRat q V₀.a₃ ∧
    0 ≤ padicValRat q V₀.a₄ ∧ 0 ≤ padicValRat q V₀.a₆ := by
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  obtain ⟨A, hA, -⟩ := ValuationSubring.exists_isFrobeniusAt_rat q hq
  obtain ⟨hm₁, hm₂, hm₃, hm₄, hm₆⟩ := quotient_coeffs_mem W hp hq hqp A hA Q hQord hn
  have hval : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := hA
  have key : ∀ r : ℚ, (r : AlgebraicClosure ℚ) ∈ A → 0 ≤ padicValRat q r := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · rw [padicValRat.zero]
    · exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hq hval hr0).mp hr
  have h₁ := congrArg WeierstrassCurve.a₁ hV₀
  have h₂ := congrArg WeierstrassCurve.a₂ hV₀
  have h₃ := congrArg WeierstrassCurve.a₃ hV₀
  have h₄ := congrArg WeierstrassCurve.a₄ hV₀
  have h₆ := congrArg WeierstrassCurve.a₆ hV₀
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_ratCast] at h₁ h₂ h₃ h₄ h₆
  exact ⟨key _ (by rw [h₁]; exact hm₁), key _ (by rw [h₂]; exact hm₂),
    key _ (by rw [h₃]; exact hm₃), key _ (by rw [h₄]; exact hm₄),
    key _ (by rw [h₆]; exact hm₆)⟩

private lemma qd1b_integrality
    (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (V₀ : WeierstrassCurve ℚ)
    (hV₀ : V₀.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
        (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q ((p - 1) / 2))) :
    ∃ e : ℕ, ∃ z₁ z₂ z₃ z₄ z₆ : ℤ,
      (z₁ : ℚ) = V₀.a₁ * (p : ℚ) ^ e ∧ (z₂ : ℚ) = V₀.a₂ * (p : ℚ) ^ (2 * e) ∧
      (z₃ : ℚ) = V₀.a₃ * (p : ℚ) ^ (3 * e) ∧ (z₄ : ℚ) = V₀.a₄ * (p : ℚ) ^ (4 * e) ∧
      (z₆ : ℚ) = V₀.a₆ * (p : ℚ) ^ (6 * e) := by
  have hn : (p - 1) / 2 < p := by have := hp.two_le; omega
  have key := fun (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) =>
    coeff_padic_nonneg W hp hq hqp Q hQord hn V₀ hV₀
  obtain ⟨e₁, hd₁⟩ := den_eq_prime_pow (p := p) (r := V₀.a₁) fun q hq hqp => (key q hq hqp).1
  obtain ⟨e₂, hd₂⟩ := den_eq_prime_pow (p := p) (r := V₀.a₂) fun q hq hqp => (key q hq hqp).2.1
  obtain ⟨e₃, hd₃⟩ := den_eq_prime_pow (p := p) (r := V₀.a₃) fun q hq hqp => (key q hq hqp).2.2.1
  obtain ⟨e₄, hd₄⟩ := den_eq_prime_pow (p := p) (r := V₀.a₄) fun q hq hqp => (key q hq hqp).2.2.2.1
  obtain ⟨e₆, hd₆⟩ := den_eq_prime_pow (p := p) (r := V₀.a₆) fun q hq hqp => (key q hq hqp).2.2.2.2
  obtain ⟨z₁, hz₁⟩ := exists_int_eq_mul_pow hd₁
    (show e₁ ≤ 1 * (e₁ + e₂ + e₃ + e₄ + e₆) by omega)
  obtain ⟨z₂, hz₂⟩ := exists_int_eq_mul_pow hd₂
    (show e₂ ≤ 2 * (e₁ + e₂ + e₃ + e₄ + e₆) by omega)
  obtain ⟨z₃, hz₃⟩ := exists_int_eq_mul_pow hd₃
    (show e₃ ≤ 3 * (e₁ + e₂ + e₃ + e₄ + e₆) by omega)
  obtain ⟨z₄, hz₄⟩ := exists_int_eq_mul_pow hd₄
    (show e₄ ≤ 4 * (e₁ + e₂ + e₃ + e₄ + e₆) by omega)
  obtain ⟨z₆, hz₆⟩ := exists_int_eq_mul_pow hd₆
    (show e₆ ≤ 6 * (e₁ + e₂ + e₃ + e₄ + e₆) by omega)
  refine ⟨e₁ + e₂ + e₃ + e₄ + e₆, z₁, z₂, z₃, z₄, z₆, ?_, hz₂, hz₃, hz₄, hz₆⟩
  rw [hz₁, one_mul]

private lemma rescale_package (V₀ : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime)
    (e : ℕ) (z₁ z₂ z₃ z₄ z₆ : ℤ)
    (h₁ : (z₁ : ℚ) = V₀.a₁ * p ^ e) (h₂ : (z₂ : ℚ) = V₀.a₂ * p ^ (2 * e))
    (h₃ : (z₃ : ℚ) = V₀.a₃ * p ^ (3 * e)) (h₄ : (z₄ : ℚ) = V₀.a₄ * p ^ (4 * e))
    (h₆ : (z₆ : ℚ) = V₀.a₆ * p ^ (6 * e)) :
    let W' : WeierstrassCurve ℤ := ⟨z₁, z₂, z₃, z₄, z₆⟩
    ∃ u : (AlgebraicClosure ℚ)ˣ,
      (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
        (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
          (V₀.map (algebraMap ℚ (AlgebraicClosure ℚ))) ∧
      (↑u : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ (-(e : ℕ) : ℤ) := by
  intro W'
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  refine ⟨(Units.mk0 (p : AlgebraicClosure ℚ) hp0)⁻¹ ^ e, ?_, ?_⟩
  ·

    have hu : ((Units.mk0 (p : AlgebraicClosure ℚ) hp0)⁻¹ ^ e : (AlgebraicClosure ℚ)ˣ)⁻¹
        = Units.mk0 (p : AlgebraicClosure ℚ) hp0 ^ e := by
      simp [inv_pow, inv_inv]
    have hcoe : ((Units.mk0 (p : AlgebraicClosure ℚ) hp0 ^ e : (AlgebraicClosure ℚ)ˣ)
        : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ e := by
      simp

    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
        WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
        WeierstrassCurve.variableChange_a₆, hu, Units.val_pow_eq_pow_val, Units.val_mk0,
        WeierstrassCurve.map, WeierstrassCurve.baseChange, mul_zero, zero_mul, sub_zero,
        add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        Int.coe_castRingHom]

    · rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) (z₁ : ℚ)
            = (algebraMap ℚ (AlgebraicClosure ℚ)) (V₀.a₁ * p ^ e) from by rw [h₁]]
      push_cast; ring
    · rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) (z₂ : ℚ)
            = (algebraMap ℚ (AlgebraicClosure ℚ)) (V₀.a₂ * p ^ (2 * e)) from by rw [h₂]]
      push_cast; ring
    · rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) (z₃ : ℚ)
            = (algebraMap ℚ (AlgebraicClosure ℚ)) (V₀.a₃ * p ^ (3 * e)) from by rw [h₃]]
      push_cast; ring
    · rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) (z₄ : ℚ)
            = (algebraMap ℚ (AlgebraicClosure ℚ)) (V₀.a₄ * p ^ (4 * e)) from by rw [h₄]]
      push_cast; ring
    · rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) (z₆ : ℚ)
            = (algebraMap ℚ (AlgebraicClosure ℚ)) (V₀.a₆ * p ^ (6 * e)) from by rw [h₆]]
      push_cast; ring
  ·
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [zpow_neg, zpow_natCast, inv_pow]

private lemma qd1b_Δ_ne_zero_of_eq_smul (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ)
    (V : WeierstrassCurve (AlgebraicClosure ℚ)) (hV : V.Δ ≠ 0)
    (heq : (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
      (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) • V) :
    W'.Δ ≠ 0 := by
  have hne : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ ≠ 0 := by
    rw [heq, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hV
  intro h0
  apply hne
  show ((W'.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ = 0
  rw [map_Δ, map_Δ, h0, _root_.map_zero, _root_.map_zero]

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (hQstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • Q ∈ AddSubgroup.zmultiples Q) :
    let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
    let S := Wb.oddOrderSummingSet Q (p / 2)
    ∃ (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ), W'.Δ ≠ 0 ∧
      (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
        (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) • Wb.veluQuotient S ∧
      ∃ e : ℤ, (u : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ e := by
  intro Wb S

  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  have hord' : addOrderOf Q = 2 * (p / 2) + 1 := by rw [hQord]; omega

  obtain ⟨V₀, hV₀⟩ :=
    WeierstrassCurve.exists_veluQuotient_descent_of_smul_mem_zmultiples
      (W := W.map (Int.castRingHom ℚ)) hp hp2 hQord hQstab

  obtain ⟨e, z₁, z₂, z₃, z₄, z₆, h₁, h₂, h₃, h₄, h₆⟩ :=
    qd1b_integrality W hp Q hQord V₀ hV₀

  obtain ⟨u, heq, hk⟩ := rescale_package V₀ hp e z₁ z₂ z₃ z₄ z₆ h₁ h₂ h₃ h₄ h₆
  set W' : WeierstrassCurve ℤ := ⟨z₁, z₂, z₃, z₄, z₆⟩ with hW'
  have hS : Wb.veluQuotient S = V₀.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    rw [hV₀, hhalf]

  have h2 : (2 : AlgebraicClosure ℚ) ≠ 0 := two_ne_zero
  haveI : Wb.IsElliptic := by
    rw [isElliptic_iff]
    refine isUnit_iff_ne_zero.mpr ?_
    show ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ≠ 0
    rw [map_Δ, map_Δ]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ Int.cast_injective).mpr hΔ)
  have hVΔ : (Wb.veluQuotient S).Δ ≠ 0 :=
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero h2 Wb (p / 2) Q hord'
  refine ⟨W', u, ?_, ?_, -(e : ℕ), hk⟩
  · rw [hS] at hVΔ
    exact qd1b_Δ_ne_zero_of_eq_smul W' u _ hVΔ heq
  · rw [hS]; exact heq

end S_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable
end P2MW
export P2MW.S_WeierstrassCurve_exists_integral_veluQuotient_rescale_of_galois_stable (solution)
