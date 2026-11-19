-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_15
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:27:24.624197+00:00
-- url     : https://prove2.me/submissions/7b078f73-f49d-4ca8-a564-57af0ed918cf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_explicit_reciprocal_truncation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section

private lemma degree_bound (q : ℕ) : (TruncationDegree q : ℝ) ≤ 64 * DegreeScale q := by
  by_cases hq : q = 0
  · subst q
    norm_num [TruncationDegree, DenominatorDegree, DegreeScale]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hsum : (DenominatorDegree q : ℝ) ≤ (2*q) * (harmonic (2*q) : ℝ) := by
    unfold DenominatorDegree harmonic
    push_cast
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      using (Nat.cast_div_le : ((2*q / (a+1) : ℕ) : ℝ) ≤ (2*q : ℕ) / (a+1 : ℕ))
  have hh := harmonic_le_one_add_log (2*q)
  have hlog : Real.log (2*q : ℝ) ≤ 2 * Real.log (q+2 : ℝ) := by
    rw [Real.log_mul (by norm_num) hqpos.ne']
    have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ q+2)
    have h₂ := Real.log_le_log hqpos (by linarith : (q : ℝ) ≤ q+2)
    linarith
  have hlower : (1 : ℝ) ≤ 2 * Real.log (q+2 : ℝ) := by
    have h₁ := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ q+2)
    have := Real.log_two_gt_d9
    linarith
  have hd : (DenominatorDegree q : ℝ) ≤ 8*q*Real.log (q+2 : ℝ) := by
    have hh' : (harmonic (2*q) : ℝ) ≤ 1 + Real.log (2*q : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
    nlinarith
  unfold TruncationDegree DegreeScale
  push_cast
  have hn : (0 : ℝ) ≤ q * Real.log (q+2 : ℝ) := mul_nonneg hqpos.le (by linarith)
  nlinarith

private lemma center_bound (N : ℕ) : (N : ℝ) ≤ Center N := by
  have hc := Nat.le_ceil ((11*N : ℝ)/40)
  unfold Center
  push_cast
  linarith

private lemma radius_bound (N : ℕ) : (Radius N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)/100 := by
  exact Nat.floor_le (by positivity)

private lemma radius_power_bound (N : ℕ) : (Radius N : ℝ)^(3/2 : ℝ) ≤ N/100 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h100 : (100 : ℝ) ≤ (100 : ℝ)^(3/2 : ℝ) := by
    calc
      (100 : ℝ) = (100 : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc
    _ ≤ ((N : ℝ)^(2/3 : ℝ)/100)^(3/2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (radius_bound N) (by norm_num)
    _ = (N : ℝ)/(100 : ℝ)^(3/2 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN]
      norm_num
    _ ≤ _ := div_le_div_of_nonneg_left hN (by norm_num) h100

private lemma factor_bound {N q : ℕ} (hN : 0 < N) (hq : (q : ℝ) ≤ (N : ℝ)^(1/3 : ℝ))
    {M l : ℝ} (hx : Rectangle N M l) (i : FactorIndex q) :
    |Eval (AffineFactor N q i) M l| ≤ 1/4 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hC : (0 : ℝ) < Center N := hNr.trans_le (center_bound N)
  have hR := radius_bound N
  have hRp := radius_power_bound N
  have hqR : (q : ℝ) * Radius N ≤ (N : ℝ)/100 := by
    calc
      _ ≤ (N : ℝ)^(1/3 : ℝ) * ((N : ℝ)^(2/3 : ℝ)/100) :=
        mul_le_mul hq hR (by positivity) (by positivity)
      _ = _ := by
        rw [← mul_div_assoc, ← Real.rpow_add hNr]
        norm_num
  have hindex : ((2*(i.val.1.val+1)-1 : ℕ) : ℝ) ≤ 4*q := by
    have h := i.val.1.isLt
    have hn : 2*(i.val.1.val+1)-1 ≤ 4*q := by omega
    exact_mod_cast hn
  have hodd : (0 : ℝ) ≤ ((2*(i.val.1.val+1)-1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ l := by have := hx.1; linarith
  have hterm : ((2*(i.val.1.val+1)-1 : ℕ) : ℝ)*l ≤ (N : ℝ)/25 := by
    have : ((2*(i.val.1.val+1)-1 : ℕ) : ℝ)*l ≤ (4*q : ℝ)*Radius N :=
      mul_le_mul hindex hx.2.1 hl (by positivity)
    nlinarith
  have hnum : |(Center N : ℝ)-M + ((2*(i.val.1.val+1)-1 : ℕ) : ℝ)*l| ≤ (N : ℝ)/20 := by
    calc
      _ ≤ |(Center N : ℝ)-M| + |((2*(i.val.1.val+1)-1 : ℕ) : ℝ)*l| := abs_add_le _ _
      _ = |M-(Center N : ℝ)| + ((2*(i.val.1.val+1)-1 : ℕ) : ℝ)*l := by
        rw [abs_sub_comm, abs_of_nonneg (mul_nonneg hodd hl)]
      _ ≤ _ := by have := hx.2.2; linarith
  simp only [AffineFactor, Eval, map_mul, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [abs_mul, abs_inv, abs_of_pos hC, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hC]
  have := center_bound N
  nlinarith

private def factorEquiv (q : ℕ) : FactorIndex q ≃ (Σ a : Fin (2*q), Fin (2*q/(a.val+1))) where
  toFun i := ⟨i.val.1, ⟨i.val.2.val,i.property⟩⟩
  invFun p := ⟨(p.1,⟨p.2.val,p.2.isLt.trans_le (Nat.div_le_self _ _)⟩),p.2.isLt⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

private lemma factor_card (q : ℕ) : Fintype.card (FactorIndex q) = DenominatorDegree q := by
  rw [Fintype.card_congr (factorEquiv q), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun a => 2*q/(a+1)) (2*q)

private lemma factor_product (q : ℕ) :
    (∏ i : FactorIndex q,
      (MvPolynomial.X 0 - MvPolynomial.C ((2*(i.val.1.val+1)-1 : ℕ) : ℝ) * MvPolynomial.X 1 : Bivariate)) =
      Denominator q := by
  calc
    _ = ∏ p : (Σ a : Fin (2*q), Fin (2*q/(a.val+1))),
        (MvPolynomial.X 0 - MvPolynomial.C ((2*(p.1.val+1)-1 : ℕ) : ℝ) * MvPolynomial.X 1 : Bivariate) :=
      Fintype.prod_equiv (factorEquiv q) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.prod_sigma]
      simp only [prod_const, card_univ, Fintype.card_fin]
      exact Fin.prod_univ_eq_prod_range
        (fun a => (MvPolynomial.X 0 - MvPolynomial.C ((2*(a+1)-1 : ℕ) : ℝ) * MvPolynomial.X 1 : Bivariate) ^ (2*q/(a+1))) (2*q)

private lemma affine_degree (N q : ℕ) (i : FactorIndex q) : (AffineFactor N q i).totalDegree ≤ 1 := by
  unfold AffineFactor
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    norm_num
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    norm_num

private lemma denominator_factorization {N : ℕ} (hN : 0 < N) (q : ℕ) :
    MvPolynomial.C ((Center N : ℝ)^DenominatorDegree q) *
      (∏ i : FactorIndex q, (1-AffineFactor N q i)) = Denominator q := by
  have hC : (Center N : ℝ) ≠ 0 := ne_of_gt ((Nat.cast_pos.mpr hN).trans_le (center_bound N))
  have ha (i : FactorIndex q) : 1-AffineFactor N q i =
      MvPolynomial.C (Center N : ℝ)⁻¹ *
        (MvPolynomial.X 0 - MvPolynomial.C ((2*(i.val.1.val+1)-1 : ℕ) : ℝ) * MvPolynomial.X 1) := by
    have hc : (MvPolynomial.C (Center N : ℝ)⁻¹ : Bivariate) * MvPolynomial.C (Center N : ℝ) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hC, map_one]
    unfold AffineFactor
    linear_combination -hc
  simp_rw [ha]
  rw [prod_mul_distrib, prod_const, card_univ, factor_card, ← map_pow, ← mul_assoc,
    ← map_mul, ← mul_pow, mul_inv_cancel₀ hC, one_pow, map_one, one_mul, factor_product]

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution :
    (∃ Cdeg : ℝ, 0 < Cdeg ∧ ∀ q : ℕ,
      (TruncationDegree q : ℝ) ≤ Cdeg * DegreeScale q) ∧
    (∀ q : ℕ → ℕ,
      Asymptotics.IsLittleO Filter.atTop (fun N => (q N : ℝ)) (fun N => (N : ℝ)^(1/3 : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (ReciprocalPolynomial N (q N)).totalDegree ≤ TruncationDegree (q N) ∧
        ∀ M l : ℝ, Rectangle N M l →
          |Eval (Denominator (q N)) M l * Eval (ReciprocalPolynomial N (q N)) M l - 1| ≤ 1/100) := by
  constructor
  · exact ⟨64,by norm_num, degree_bound⟩
  · intro q hq
    obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (hq.bound (by norm_num : (0 : ℝ) < 1))
    refine ⟨max N₀ 1, ?_⟩
    intro N hN
    have hNpos : 0 < N := by omega
    have hqN := hN₀ N (le_trans (le_max_left _ _) hN)
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ q N from Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg _) (1/3 : ℝ)), one_mul] at hqN
    have hC : (0 : ℝ) < Center N := (Nat.cast_pos.mpr hNpos).trans_le (center_bound N)
    have h := explicit_reciprocal_truncation (AffineFactor N (q N)) (affine_degree N (q N))
      ((Center N : ℝ)^DenominatorDegree (q N)) (pow_pos hC _)
    constructor
    · simpa only [factor_card, ReciprocalPolynomial, TruncationDegree, Nat.add_assoc] using h.1
    · intro M l hx
      have hb := h.2 M l (fun i => factor_bound hNpos hqN hx i)
      rw [denominator_factorization hNpos (q N)] at hb
      simpa only [factor_card, ReciprocalPolynomial, TruncationDegree, Nat.add_assoc] using hb
