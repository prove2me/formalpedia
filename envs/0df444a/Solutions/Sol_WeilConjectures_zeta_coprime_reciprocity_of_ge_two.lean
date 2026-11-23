-- Prove2me | solution 1 for WeilConjectures.zeta_coprime_reciprocity_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:13:33.510933+00:00
-- url     : https://prove2.me/submissions/f24abefd-0ee5-4e82-8832-ae8eefc67011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_zeta_functional_equation_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section CoprimeReciprocity

private lemma coeff_comp_C_mul_X (P : ℚ[X]) (a : ℚ) (j : ℕ) :
    (P.comp (C a * X)).coeff j = P.coeff j * a ^ j := by
  induction P using Polynomial.induction_on' generalizing j with
  | add p q hp hq =>
    simp [Polynomial.add_comp, hp, hq, add_mul]
  | monomial n r =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    by_cases h : n = j
    · subst h; simp
    · simp [h]

private lemma comp_C_mul_X_ne_zero {P : ℚ[X]} (hP : P ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    P.comp (C a * X) ≠ 0 := by
  intro h0
  apply hP
  ext j
  have hj := congrArg (fun f : ℚ[X] => f.coeff j) h0
  rw [coeff_comp_C_mul_X, Polynomial.coeff_zero] at hj
  exact (mul_eq_zero.mp hj).resolve_right (pow_ne_zero j ha)

private lemma natDegree_comp_C_mul_X (P : ℚ[X]) {a : ℚ} (ha : a ≠ 0) :
    (P.comp (C a * X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ ha, mul_one]

private lemma coeff_reverse_comp_C_mul_X (P : ℚ[X]) {a : ℚ} (ha : a ≠ 0) (m : ℕ) :
    ((P.comp (C a * X)).reverse).coeff m =
      if m ≤ P.natDegree then P.coeff (P.natDegree - m) * a ^ (P.natDegree - m) else 0 := by
  have hdeg_comp : (P.comp (C a * X)).natDegree = P.natDegree := natDegree_comp_C_mul_X P ha
  by_cases hm : m ≤ P.natDegree
  · rw [if_pos hm, Polynomial.coeff_reverse, ← hdeg_comp,
      Polynomial.revAt_le (hdeg_comp.symm ▸ hm), hdeg_comp, coeff_comp_C_mul_X]
  · rw [if_neg hm, Polynomial.coeff_reverse, hdeg_comp,
      Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hm), coeff_comp_C_mul_X,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hm), zero_mul]

private lemma reverse_natDegree_of_coeff_zero_ne_zero {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    P.reverse.natDegree = P.natDegree := by
  have htrail : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP0)
  rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]

private lemma reverse_reverse_of_coeff_zero_ne_zero {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    P.reverse.reverse = P := by
  have hdeg : P.reverse.natDegree = P.natDegree := reverse_natDegree_of_coeff_zero_ne_zero hP0
  ext m
  rw [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_reverse, Polynomial.revAt_invol]

private lemma monic_reverse_of_coeff_zero_eq_one {P : ℚ[X]} (hP0 : P.coeff 0 = 1) :
    P.reverse.Monic := by
  have hP0_ne : P.coeff 0 ≠ 0 := by rw [hP0]; exact one_ne_zero
  rw [Polynomial.Monic, Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP0_ne), hP0]

private noncomputable def poincareDual (a : ℚ) (P : ℚ[X]) : ℚ[X] :=
  C (P.coeff 0)⁻¹ * (P.comp (C a * X)).reverse

private lemma poincareDual_natDegree {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).natDegree = P.natDegree := by
  unfold poincareDual
  have hcomp0 : (P.comp (C a * X)).coeff 0 ≠ 0 := by
    rw [coeff_comp_C_mul_X, pow_zero, mul_one]; exact hP0
  have hrev_deg : ((P.comp (C a * X)).reverse).natDegree = P.natDegree := by
    rw [reverse_natDegree_of_coeff_zero_ne_zero hcomp0, natDegree_comp_C_mul_X P ha]
  rw [Polynomial.natDegree_C_mul (inv_ne_zero hP0), hrev_deg]

private lemma poincareDual_monic {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, poincareDual_natDegree ha hP0]
  unfold poincareDual
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha, if_pos le_rfl,
    Nat.sub_self, pow_zero, mul_one, inv_mul_cancel₀ hP0]

private lemma poincareDual_coeff_zero {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP : P.Monic) :
    (poincareDual a P).coeff 0 = (P.coeff 0)⁻¹ * a ^ P.natDegree := by
  unfold poincareDual
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha, if_pos (Nat.zero_le _),
    Nat.sub_zero, hP.coeff_natDegree, one_mul]

private lemma poincareDual_coeff_zero_ne_zero {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]}
    (hP : P.Monic) (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).coeff 0 ≠ 0 := by
  rw [poincareDual_coeff_zero ha hP]
  exact mul_ne_zero (inv_ne_zero hP0) (pow_ne_zero _ ha)

private lemma poincareDual_mul {a : ℚ} (P Q : ℚ[X]) :
    poincareDual a (P * Q) = poincareDual a P * poincareDual a Q := by
  unfold poincareDual
  rw [Polynomial.mul_coeff_zero, mul_inv_rev, mul_comm (Q.coeff 0)⁻¹,
    Polynomial.mul_comp, Polynomial.reverse_mul_of_domain, map_mul]
  ring

private lemma poincareDual_invol {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]}
    (hP : P.Monic) (hP0 : P.coeff 0 ≠ 0) :
    poincareDual a (poincareDual a P) = P := by
  have hDdeg : (poincareDual a P).natDegree = P.natDegree := poincareDual_natDegree ha hP0
  have hD0 : (poincareDual a P).coeff 0 = (P.coeff 0)⁻¹ * a ^ P.natDegree :=
    poincareDual_coeff_zero ha hP
  ext m
  conv_lhs => rw [poincareDual]
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X (poincareDual a P) ha, hDdeg]
  by_cases hm : m ≤ P.natDegree
  · rw [if_pos hm, hD0]
    conv_lhs => rw [poincareDual]
    rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha,
      if_pos (Nat.sub_le _ _), Nat.sub_sub_self hm]
    have hpow : a ^ m * a ^ (P.natDegree - m) = a ^ P.natDegree := by
      rw [← pow_add, Nat.add_sub_of_le hm]
    have ha_pow : a ^ P.natDegree ≠ 0 := pow_ne_zero _ ha
    calc
      ((P.coeff 0)⁻¹ * a ^ P.natDegree)⁻¹ * ((P.coeff 0)⁻¹ * (P.coeff m * a ^ m) * a ^ (P.natDegree - m))
          = (P.coeff 0 * (a ^ P.natDegree)⁻¹) * ((P.coeff 0)⁻¹ * (P.coeff m * (a ^ m * a ^ (P.natDegree - m)))) := by
            rw [mul_inv, inv_inv]; ring
      _ = P.coeff m * (P.coeff 0 * (P.coeff 0)⁻¹) * (a ^ P.natDegree * (a ^ P.natDegree)⁻¹) := by
            rw [hpow]; ring
      _ = P.coeff m := by
            rw [mul_inv_cancel₀ hP0, mul_inv_cancel₀ ha_pow, mul_one, mul_one]
  · rw [if_neg hm, mul_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hm)]

private lemma isCoprime_of_isUnit_gcd {P Q : ℚ[X]} (h : IsUnit (EuclideanDomain.gcd P Q)) :
    IsCoprime P Q := by
  rcases h with ⟨u, hu⟩
  refine ⟨C (↑u⁻¹ : ℚ[X]).leadingCoeff * EuclideanDomain.gcdA P Q,
    C (↑u⁻¹ : ℚ[X]).leadingCoeff * EuclideanDomain.gcdB P Q, ?_⟩
  have hbez : EuclideanDomain.gcd P Q = P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q :=
    EuclideanDomain.gcd_eq_gcd_ab P Q
  have hu_eq : (↑u⁻¹ : ℚ[X]) = C (↑u⁻¹ : ℚ[X]).leadingCoeff := by
    have hdeg0 : (↑u⁻¹ : ℚ[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u⁻¹.isUnit
    rw [Polynomial.leadingCoeff, hdeg0]
    exact Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  calc
    (C (↑u⁻¹ : ℚ[X]).leadingCoeff * EuclideanDomain.gcdA P Q) * P +
        (C (↑u⁻¹ : ℚ[X]).leadingCoeff * EuclideanDomain.gcdB P Q) * Q
        = (↑u⁻¹ : ℚ[X]) * (P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q) := by
          rw [← hu_eq]; ring
    _ = (↑u⁻¹ : ℚ[X]) * EuclideanDomain.gcd P Q := by rw [← hbez]
    _ = (↑u⁻¹ : ℚ[X]) * (u : ℚ[X]) := by rw [← hu]
    _ = 1 := by exact_mod_cast u.inv_mul

private lemma isCoprime_reverse {N D : ℚ[X]} (hcop : IsCoprime N D)
    (hN0 : N.coeff 0 ≠ 0) (hD0 : D.coeff 0 ≠ 0) :
    IsCoprime N.reverse D.reverse := by
  have hN_ne : N ≠ 0 := fun h => hN0 (by simp [h])
  have hNr0 : N.reverse.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hN_ne
  let d := EuclideanDomain.gcd N.reverse D.reverse
  have hdN : d ∣ N.reverse := EuclideanDomain.gcd_dvd_left N.reverse D.reverse
  have hdD : d ∣ D.reverse := EuclideanDomain.gcd_dvd_right N.reverse D.reverse
  have hd0 : d.coeff 0 ≠ 0 := by
    intro h0
    rcases hdN with ⟨u, hu⟩
    have := congrArg (fun p : ℚ[X] => p.coeff 0) hu
    rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
    exact hNr0 this
  have hd_ne : d ≠ 0 := fun h => hd0 (by simp [h])
  have hdrev_N : d.reverse ∣ N := by
    rcases hdN with ⟨u, hu⟩
    refine ⟨u.reverse, ?_⟩
    have := congrArg Polynomial.reverse hu
    rw [reverse_reverse_of_coeff_zero_ne_zero hN0, Polynomial.reverse_mul_of_domain] at this
    exact this
  have hdrev_D : d.reverse ∣ D := by
    rcases hdD with ⟨v, hv⟩
    refine ⟨v.reverse, ?_⟩
    have := congrArg Polynomial.reverse hv
    rw [reverse_reverse_of_coeff_zero_ne_zero hD0, Polynomial.reverse_mul_of_domain] at this
    exact this
  have hu_rev : IsUnit d.reverse := hcop.isUnit_of_dvd' hdrev_N hdrev_D
  have hdeg0 : d.natDegree = 0 := by
    rw [← reverse_natDegree_of_coeff_zero_ne_zero hd0]
    exact Polynomial.natDegree_eq_zero_of_isUnit hu_rev
  have hu_d : IsUnit d :=
    Polynomial.isUnit_iff_degree_eq_zero.mpr
      ((Polynomial.degree_eq_natDegree hd_ne).trans (by exact_mod_cast hdeg0))
  exact isCoprime_of_isUnit_gcd hu_d

private lemma isCoprime_poincareDual {a : ℚ} (ha : a ≠ 0) {A B : ℚ[X]}
    (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hA0 : A.coeff 0 ≠ 0) (hB0 : B.coeff 0 ≠ 0) :
    IsCoprime (poincareDual a A) (poincareDual a B) := by
  let d := EuclideanDomain.gcd (poincareDual a A) (poincareDual a B)
  have hdA : d ∣ poincareDual a A := EuclideanDomain.gcd_dvd_left _ _
  have hdB : d ∣ poincareDual a B := EuclideanDomain.gcd_dvd_right _ _
  have hDA0 : (poincareDual a A).coeff 0 ≠ 0 := poincareDual_coeff_zero_ne_zero ha hA hA0
  have hd0 : d.coeff 0 ≠ 0 := by
    intro h0
    rcases hdA with ⟨u, hu⟩
    have := congrArg (fun p : ℚ[X] => p.coeff 0) hu
    rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
    exact hDA0 this
  have hd_ne : d ≠ 0 := fun h => hd0 (by simp [h])
  have hduA : poincareDual a d ∣ A := by
    rcases hdA with ⟨u, hu⟩
    refine ⟨poincareDual a u, ?_⟩
    have := congrArg (poincareDual a) hu
    rw [poincareDual_invol ha hA hA0, poincareDual_mul] at this
    exact this
  have hduB : poincareDual a d ∣ B := by
    rcases hdB with ⟨v, hv⟩
    refine ⟨poincareDual a v, ?_⟩
    have := congrArg (poincareDual a) hv
    rw [poincareDual_invol ha hB hB0, poincareDual_mul] at this
    exact this
  have hu_dual : IsUnit (poincareDual a d) := hcop.isUnit_of_dvd' hduA hduB
  have hdeg0 : d.natDegree = 0 := by
    rw [← poincareDual_natDegree ha hd0]
    exact Polynomial.natDegree_eq_zero_of_isUnit hu_dual
  have hu_d : IsUnit d :=
    Polynomial.isUnit_iff_degree_eq_zero.mpr
      ((Polynomial.degree_eq_natDegree hd_ne).trans (by exact_mod_cast hdeg0))
  exact isCoprime_of_isUnit_gcd hu_d

private lemma eq_of_monic_dvd_same_natDegree {P Q : ℚ[X]}
    (hP : P.Monic) (hQ : Q.Monic) (hdvd : P ∣ Q) (hdeg : P.natDegree = Q.natDegree) :
    P = Q := by
  rcases hdvd with ⟨u, hu⟩
  have hu_ne : u ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hu; exact hQ.ne_zero hu
  have hu_deg0 : u.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hP.ne_zero hu_ne
    rw [← hu, ← hdeg] at hmul
    omega
  have hu_lc : u.leadingCoeff = 1 := by
    have := congrArg Polynomial.leadingCoeff hu
    rw [hQ.leadingCoeff, Polynomial.leadingCoeff_mul, hP.leadingCoeff, one_mul] at this
    exact this.symm
  have hu_eq1 : u = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hu_deg0]
    have h0 : u.coeff 0 = 1 := by
      have : u.leadingCoeff = u.coeff 0 := by rw [Polynomial.leadingCoeff, hu_deg0]
      rwa [← this]
    rw [h0, map_one]
  rw [hu, hu_eq1, mul_one]

end CoprimeReciprocity

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (N D : ℚ[X]) (hcop : IsCoprime N D) (hN0 : N.coeff 0 = 1) (hD0 : D.coeff 0 = 1)
    (hzeta : zetaFunction p f * (D : PowerSeries ℚ) = (N : PowerSeries ℚ)) :
    (N.reverse.coeff 0 • N.reverse =
      (N.reverse.comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X)).reverse) ∧
    (D.reverse.coeff 0 • D.reverse =
      (D.reverse.comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X)).reverse) := by
  obtain ⟨P, Q, c, hQ_ne, hc_ne, hPQ_zeta, hfe⟩ :=
    WeilConjectures.exists_zeta_functional_equation_of_ge_two p k n hn X f hproj
  have hN0_ne : N.coeff 0 ≠ 0 := by rw [hN0]; exact one_ne_zero
  have hD0_ne : D.coeff 0 ≠ 0 := by rw [hD0]; exact one_ne_zero
  have hN_ne : N ≠ 0 := fun h => hN0_ne (by simp [h])
  have hD_ne : D ≠ 0 := fun h => hD0_ne (by simp [h])
  -- Relate (P, Q) to the coprime presentation (N, D): P * D = N * Q
  have hPD_NQ_ps : ((P * D : ℚ[X]) : PowerSeries ℚ) = ((N * Q : ℚ[X]) : PowerSeries ℚ) := by
    calc
      ((P * D : ℚ[X]) : PowerSeries ℚ)
          = (P : PowerSeries ℚ) * (D : PowerSeries ℚ) := Polynomial.coe_mul P D
      _ = (zetaFunction p f * (Q : PowerSeries ℚ)) * (D : PowerSeries ℚ) := by rw [hPQ_zeta]
      _ = (zetaFunction p f * (D : PowerSeries ℚ)) * (Q : PowerSeries ℚ) := by ring
      _ = (N : PowerSeries ℚ) * (Q : PowerSeries ℚ) := by rw [hzeta]
      _ = ((N * Q : ℚ[X]) : PowerSeries ℚ) := (Polynomial.coe_mul N Q).symm
  have hPD_NQ : P * D = N * Q := Polynomial.coe_injective (R := ℚ) hPD_NQ_ps
  have hD_dvd_Q : D ∣ Q := hcop.symm.dvd_of_dvd_mul_left ⟨P, by rw [← hPD_NQ, mul_comm]⟩
  rcases hD_dvd_Q with ⟨g, hQ_eq⟩
  have hg_ne : g ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ_eq; exact hQ_ne hQ_eq
  have hP_eq : P = N * g := by
    have : P * D = (N * g) * D := by rw [hPD_NQ, hQ_eq]; ring
    exact mul_right_cancel₀ hD_ne this
  let a : ℚ := (Nat.card k : ℚ) ^ n
  have ha_ne : a ≠ 0 := by
    have : 0 < Nat.card k := Nat.card_pos
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt this))
  have hfe_ND :
      (N.reverse.comp (C a * Polynomial.X)) * D =
        C c * (N * (D.reverse.comp (C a * Polynomial.X))) := by
    have hgrev_ne : g.reverse ≠ 0 := by
      intro h0; exact hg_ne (Polynomial.reverse_eq_zero.mp h0)
    have hcomp_g_ne : g.reverse.comp (C a * Polynomial.X) ≠ 0 :=
      comp_C_mul_X_ne_zero hgrev_ne ha_ne
    have hfac_ne : g * g.reverse.comp (C a * Polynomial.X) ≠ 0 := mul_ne_zero hg_ne hcomp_g_ne
    apply mul_left_cancel₀ hfac_ne
    have hfe' :
        ((N * g).reverse.comp (C a * Polynomial.X)) * (D * g) =
          C c * ((N * g) * ((D * g).reverse.comp (C a * Polynomial.X))) := by
      simpa [a, hP_eq, hQ_eq] using hfe
    rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_mul_of_domain,
      Polynomial.mul_comp, Polynomial.mul_comp] at hfe'
    calc
      (g * g.reverse.comp (C a * Polynomial.X)) * (N.reverse.comp (C a * Polynomial.X) * D)
          = (N.reverse.comp (C a * Polynomial.X) * g.reverse.comp (C a * Polynomial.X)) * (D * g) := by
            ring
      _ = C c * (N * g * (D.reverse.comp (C a * Polynomial.X) * g.reverse.comp (C a * Polynomial.X))) :=
            hfe'
      _ = (g * g.reverse.comp (C a * Polynomial.X)) *
            (C c * (N * D.reverse.comp (C a * Polynomial.X))) := by ring
  -- Take .reverse of both sides and express in terms of A = N.reverse, B = D.reverse
  let A : ℚ[X] := N.reverse
  let B : ℚ[X] := D.reverse
  have hA_monic : A.Monic := monic_reverse_of_coeff_zero_eq_one hN0
  have hB_monic : B.Monic := monic_reverse_of_coeff_zero_eq_one hD0
  have hA0 : A.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hN_ne
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hD_ne
  have hcop_AB : IsCoprime A B := isCoprime_reverse hcop hN0_ne hD0_ne
  have hcop_dAdB : IsCoprime (poincareDual a A) (poincareDual a B) :=
    isCoprime_poincareDual ha_ne hcop_AB hA_monic hB_monic hA0 hB0
  have hrev_fe := congrArg Polynomial.reverse hfe_ND
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_mul_of_domain,
    Polynomial.reverse_mul_of_domain, Polynomial.reverse_C] at hrev_fe
  have hA_comp : (A.comp (C a * Polynomial.X)).reverse = C (A.coeff 0) * poincareDual a A := by
    unfold poincareDual
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hA0, map_one, one_mul]
  have hB_comp : (B.comp (C a * Polynomial.X)).reverse = C (B.coeff 0) * poincareDual a B := by
    unfold poincareDual
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hB0, map_one, one_mul]
  have hbal :
      C (A.coeff 0) * (poincareDual a A * B) = C (c * B.coeff 0) * (A * poincareDual a B) := by
    change (A.comp (C a * Polynomial.X)).reverse * B =
      C c * (A * (B.comp (C a * Polynomial.X)).reverse) at hrev_fe
    rw [hA_comp, hB_comp] at hrev_fe
    rw [map_mul]
    calc
      C (A.coeff 0) * (poincareDual a A * B) = C (A.coeff 0) * poincareDual a A * B := by ring
      _ = C c * (A * (C (B.coeff 0) * poincareDual a B)) := hrev_fe
      _ = C c * C (B.coeff 0) * (A * poincareDual a B) := by ring
  have hcB_ne : c * B.coeff 0 ≠ 0 := mul_ne_zero hc_ne hB0
  have hdA_dvd_A : poincareDual a A ∣ A := by
    have hdvd_prod : poincareDual a A ∣ A * poincareDual a B := by
      refine ⟨C ((c * B.coeff 0)⁻¹ * A.coeff 0) * B, ?_⟩
      calc
        A * poincareDual a B
            = C (c * B.coeff 0)⁻¹ * (C (c * B.coeff 0) * (A * poincareDual a B)) := by
              rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcB_ne, map_one, one_mul]
        _ = C (c * B.coeff 0)⁻¹ * (C (A.coeff 0) * (poincareDual a A * B)) := by rw [← hbal]
        _ = poincareDual a A * (C ((c * B.coeff 0)⁻¹ * A.coeff 0) * B) := by rw [map_mul]; ring
    exact hcop_dAdB.dvd_of_dvd_mul_right hdvd_prod
  have hB_dvd_dB : B ∣ poincareDual a B := by
    have hdvd_prod : B ∣ A * poincareDual a B := by
      refine ⟨C ((c * B.coeff 0)⁻¹ * A.coeff 0) * poincareDual a A, ?_⟩
      calc
        A * poincareDual a B
            = C (c * B.coeff 0)⁻¹ * (C (c * B.coeff 0) * (A * poincareDual a B)) := by
              rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcB_ne, map_one, one_mul]
        _ = C (c * B.coeff 0)⁻¹ * (C (A.coeff 0) * (poincareDual a A * B)) := by rw [← hbal]
        _ = B * (C ((c * B.coeff 0)⁻¹ * A.coeff 0) * poincareDual a A) := by rw [map_mul]; ring
    exact hcop_AB.symm.dvd_of_dvd_mul_left hdvd_prod
  have hdA_eq : poincareDual a A = A :=
    eq_of_monic_dvd_same_natDegree (poincareDual_monic ha_ne hA0) hA_monic hdA_dvd_A
      (poincareDual_natDegree ha_ne hA0)
  have hB_eq : B = poincareDual a B :=
    eq_of_monic_dvd_same_natDegree hB_monic (poincareDual_monic ha_ne hB0) hB_dvd_dB
      (poincareDual_natDegree ha_ne hB0).symm
  refine ⟨?_, ?_⟩
  · change A.coeff 0 • A = (A.comp (C a * Polynomial.X)).reverse
    rw [hA_comp, hdA_eq, Polynomial.smul_eq_C_mul]
  · change B.coeff 0 • B = (B.comp (C a * Polynomial.X)).reverse
    rw [hB_comp, ← hB_eq, Polynomial.smul_eq_C_mul]
