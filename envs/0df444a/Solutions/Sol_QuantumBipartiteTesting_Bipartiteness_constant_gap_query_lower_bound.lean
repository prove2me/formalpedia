-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.constant_gap_query_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:09:05.183528+00:00
-- url     : https://prove2.me/submissions/053937ff-039a-46bf-8112-55ce9e4b3d1f

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_proposition_3_13
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_zero_anchored_grid_degree
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_explicit_reciprocal_truncation
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness
noncomputable section
open Finset MvPolynomial
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private lemma xor_star {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    star (QAlgorithms.xorOracle f) = QAlgorithms.xorOracle (-f) := by
  ext ⟨i,y⟩ ⟨j,z⟩
  by_cases h : i = j
  · subst j
    simp [QAlgorithms.xorOracle, Matrix.star_apply, eq_add_neg_iff_add_eq, eq_comm]
  · simp [QAlgorithms.xorOracle, Matrix.star_apply, h, Ne.symm h]

private lemma xor_unitary {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    QAlgorithms.xorOracle f ∈ Matrix.unitaryGroup (I × K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, xor_star]
  exact QAlgorithms.xorOracle_mul_neg f

private lemma final_norm {I : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (A : Algorithm I k w q) (O : Matrix (I × Bits k) (I × Bits k) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (I × Bits k) ℂ) : ‖A.finalState O‖ = 1 := by
  have hK : Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ) ∈
      Matrix.unitaryGroup ((I × Bits k) × Fin w) ℂ :=
    Matrix.kronecker_mem_unitary hO (one_mem _)
  have hstate : ∀ t, ‖A.stateAt O t‖ = 1 := by
    apply Fin.induction
    · change ‖QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) A.start‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U 0).property, A.start_unit]
    · intro i ih
      change ‖QAlgorithms.act (A.U i.succ : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ))
          (A.stateAt O i.castSucc))‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U i.succ).property,
        QAlgorithms.act_norm_of_mem_unitaryGroup hK, ih]
  exact hstate _

private lemma accept_bounds {I S : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (O : I → Option S) :
    0 ≤ Accept E A out O ∧ Accept E A out O ≤ 1 := by
  have hnorm := final_norm A _ (xor_unitary (E.code ∘ O))
  constructor
  · exact sum_nonneg (fun _ _ => sq_nonneg _)
  · unfold Accept QAlgorithms.QueryAlg.outputProb QAlgorithms.probEvent
    calc
      _ ≤ ∑ z, QAlgorithms.prob (A.finalState (QAlgorithms.xorOracle (E.code ∘ O))) z := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro z hz hz'
        exact sq_nonneg _
      _ = ‖A.finalState (QAlgorithms.xorOracle (E.code ∘ O))‖^2 := by
        simp only [QAlgorithms.prob, QAlgorithms.ket, EuclideanSpace.inner_single_left,
          EuclideanSpace.norm_sq_eq, map_one, one_mul]
      _ = 1 := by rw [hnorm]; norm_num


private lemma average_bounds {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ Average s f ∧ Average s f ≤ 1 := by
  unfold Average
  constructor
  · exact div_nonneg (sum_nonneg (fun x hx => (hf x hx).1)) (Nat.cast_nonneg _)
  · by_cases hs : s.card = 0
    · simp [hs]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hs)).mpr
      calc
        _ ≤ ∑ x ∈ s, (1:ℝ) := sum_le_sum (fun x hx => (hf x hx).2)
        _ = _ := by simp


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

private lemma reciprocal_bound (N q : ℕ) (hN : 0 < N) (hq : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ)) :
    (ReciprocalPolynomial N q).totalDegree ≤ TruncationDegree q ∧
      ∀ M l : ℝ, Rectangle N M l →
        |Eval (Denominator q) M l*Eval (ReciprocalPolynomial N q) M l-1| ≤ 1/100 := by
  have hC : (0:ℝ) < Center N := (Nat.cast_pos.mpr hN).trans_le (center_bound N)
  have h := explicit_reciprocal_truncation (AffineFactor N q) (affine_degree N q)
    ((Center N:ℝ)^DenominatorDegree q) (pow_pos hC _)
  constructor
  · simpa only [factor_card,ReciprocalPolynomial,TruncationDegree,Nat.add_assoc] using h.1
  · intro M l hx
    have hb := h.2 M l (fun i => factor_bound hN hq hx i)
    rw [denominator_factorization hN q] at hb
    simpa only [factor_card,ReciprocalPolynomial,TruncationDegree,Nat.add_assoc] using hb

private lemma feasible_acceptance_bounds {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q) (out : (Address N colors × Bits k) × Fin w → Bool)
    (s : Signing) (M l : ℕ) :
    0 ≤ FeasibleAcceptance E A out s M l ∧ FeasibleAcceptance E A out s M l ≤ 1 := by
  unfold FeasibleAcceptance FeasibleBase MatchingAverage
  apply average_bounds
  intro b hb
  apply average_bounds
  intro t ht
  apply average_bounds
  intro h hh
  cases s <;> unfold SigningAverage <;> apply average_bounds <;> intro x hx <;> exact accept_bounds E A out _

private lemma feasible_gap_bound {N colors k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N colors) k w q) (out : (Address N colors × Bits k) × Fin w → Bool)
    (M l : ℕ) : |FeasibleGap E A out M l| ≤ 1 := by
  have hy := feasible_acceptance_bounds E A out .yes M l
  have hn := feasible_acceptance_bounds E A out .no M l
  exact abs_le.mpr ⟨by unfold FeasibleGap; linarith,by unfold FeasibleGap; linarith⟩

private def GapPolynomial (N q : ℕ) (H : Bivariate) : Bivariate :=
  C (1/2:ℝ)*X 1*H*ReciprocalPolynomial N q

private lemma gap_polynomial_degree (N q : ℕ) (H : Bivariate) :
    (GapPolynomial N q H).totalDegree ≤ 1+H.totalDegree+(ReciprocalPolynomial N q).totalDegree := by
  have h₁ := totalDegree_mul (C (1/2:ℝ) : Bivariate) (X 1)
  have h₂ := totalDegree_mul (C (1/2:ℝ)*X 1 : Bivariate) H
  have h₃ := totalDegree_mul (C (1/2:ℝ)*X 1*H : Bivariate) (ReciprocalPolynomial N q)
  simp only [totalDegree_C,totalDegree_X] at h₁
  unfold GapPolynomial
  omega

private lemma gap_polynomial_eval {N k w q M l : ℕ} (H : Bivariate)
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N 3) k w q)
    (out : (Address N 3 × Bits k) × Fin w → Bool)
    (hD : Eval (Denominator q) M l ≠ 0)
    (hid : FeasibleGap E A out M l = l*Eval H M l/Eval (Denominator q) M l+GapError E A out M l) :
    Eval (GapPolynomial N q H) M l =
      ((FeasibleGap E A out M l-GapError E A out M l)/2)*
        (Eval (Denominator q) M l*Eval (ReciprocalPolynomial N q) M l) := by
  have hraw : FeasibleGap E A out M l-GapError E A out M l = l*Eval H M l/Eval (Denominator q) M l := by linarith
  rw [hraw]
  simp only [GapPolynomial,Eval,map_mul,eval_C,eval_X,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  change MvPolynomial.eval ![(M:ℝ),(l:ℝ)] (Denominator q) ≠ 0 at hD
  field_simp [hD]
  <;> ring

private def ScaleFirst (P : Bivariate) : Bivariate := P.eval₂ MvPolynomial.C ![C 2*X 0,X 1]

private lemma scale_first_degree (P : Bivariate) : (ScaleFirst P).totalDegree ≤ P.totalDegree := by
  unfold ScaleFirst
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply (sum_le_sum (fun i hi => ?_)).trans (MvPolynomial.le_totalDegree hd)
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have hi : (![C 2*X 0,X 1] i : Bivariate).totalDegree ≤ 1 := by
    fin_cases i
    · simpa using totalDegree_mul (C (2:ℝ) : Bivariate) (X 0)
    · simp
  simpa using Nat.mul_le_mul_left (d i) hi

private lemma scale_first_eval (P : Bivariate) (M l : ℝ) : Eval (ScaleFirst P) M l = Eval P (2*M) l := by
  unfold ScaleFirst Eval
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![M,l]
    (P.eval₂ MvPolynomial.C ![C 2*X 0,X 1]) = P.eval₂ (RingHom.id ℝ) ![2*M,l]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (MvPolynomial.eval₂Hom (RingHom.id ℝ) ![M,l]).comp MvPolynomial.C = RingHom.id ℝ := by ext x; simp
  have hv : (MvPolynomial.eval₂Hom (RingHom.id ℝ) ![M,l]) ∘ ![C 2*X 0,X 1] = ![2*M,l] := by
    funext i
    fin_cases i <;> simp
  rw [hc,hv]

private lemma radius_lower (N : ℕ) (hN : 0 < N) (hlarge : (20:ℝ) ≤ (N:ℝ)^(1/3:ℝ)) :
    2 ≤ Radius N ∧ (N:ℝ)^(1/3:ℝ)/20 ≤ Real.sqrt (Radius N) := by
  have hpow : (N:ℝ)^(2/3:ℝ) = ((N:ℝ)^(1/3:ℝ))^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hf : (N:ℝ)^(2/3:ℝ)/100 < (Radius N:ℝ)+1 := Nat.lt_floor_add_one _
  rw [hpow] at hf
  have hsquare : (400:ℝ) ≤ ((N:ℝ)^(1/3:ℝ))^2 := by nlinarith
  constructor
  · exact_mod_cast (show (2:ℝ) ≤ Radius N by nlinarith)
  · apply Real.le_sqrt_of_sq_le
    nlinarith

private lemma scale_upper {N q : ℕ} (hN : 2 ≤ N) (hq : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ)) :
    DegreeScale q ≤ 1+2*q*Real.log N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hqN : (q:ℝ) ≤ N := hq.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/3:ℝ) ≤ 1))
  have hN2r : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log (q+2:ℝ) ≤ 2*Real.log N := by
    have h₁ := Real.log_le_log (by positivity : (0:ℝ) < q+2)
      (show (q+2:ℝ) ≤ 2*N by linarith)
    have h₂ := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hN : (2:ℝ) ≤ N)
    rw [Real.log_mul (by norm_num) (by positivity : (N:ℝ) ≠ 0)] at h₁
    linarith
  unfold DegreeScale
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0:ℝ) ≤ q)
  nlinarith

private lemma center_even (N : ℕ) : 2*(Center N/2) = Center N := by unfold Center; omega

private lemma natural_grid {N : ℕ} (hN : 0 < N) {X l : ℤ}
    (hl : 1 ≤ l) (hlR : l ≤ (Radius N:ℤ))
    (hwindow : |(X:ℝ)-(Center N/2:ℕ)| ≤ (Radius N:ℝ)^(3/2:ℝ)/2)
    (hdiv : l ∣ X) :
    Grid N (2*X.toNat) l.toNat ∧ (X.toNat:ℝ) = X ∧ (l.toNat:ℝ) = l := by
  have hc := center_bound N
  have hce := congrArg (fun x : ℕ => (x:ℝ)) (center_even N)
  push_cast at hce
  have hrad := radius_power_bound N
  have hX : (0:ℝ) ≤ X := by have hh := (abs_le.mp hwindow).1; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hXint : 0 ≤ X := by exact_mod_cast hX
  have hL : 0 ≤ l := by omega
  have hxi : (X.toNat:ℤ) = X := Int.toNat_of_nonneg hXint
  have hli : (l.toNat:ℤ) = l := Int.toNat_of_nonneg hL
  have hxr : (X.toNat:ℝ) = X := by exact_mod_cast hxi
  have hlr : (l.toNat:ℝ) = l := by exact_mod_cast hli
  refine ⟨⟨by exact_mod_cast (show (1:ℤ) ≤ (l.toNat:ℤ) by simpa only [hli] using hl),
    by exact_mod_cast (show (l.toNat:ℤ) ≤ (Radius N:ℤ) by simpa only [hli] using hlR),?_,?_⟩,hxr,hlr⟩
  · push_cast
    rw [hxr,← hce,show (2:ℝ)*X-2*(Center N/2:ℕ) = 2*((X:ℝ)-(Center N/2:ℕ)) by ring,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  · have hd : l.toNat ∣ X.toNat := by
      have hh : (l.toNat:ℤ) ∣ (X.toNat:ℤ) := by simpa only [hxi,hli] using hdiv
      exact_mod_cast hh
    exact Nat.mul_dvd_mul_left 2 hd

private lemma approximate_gap_bounds (g e z r : ℝ)
    (hr : r = ((g-e)/2)*z) (hg : |g| ≤ 1) (he : |e| ≤ 1/1000) (hz : |z-1| ≤ 1/100) :
    |r| ≤ 1 ∧ (1/4 ≤ g → 1/10 ≤ r) := by
  have hge : |g-e| ≤ 1001/1000 := by
    have hh := abs_sub_le g 0 e
    simp only [sub_zero,zero_sub,abs_neg] at hh
    linarith
  have hzabs : |z| ≤ 101/100 := by
    have hh := abs_sub_le z 1 0
    simp only [sub_zero,abs_one] at hh
    linarith
  have hprod : |r| ≤ (1001/2000:ℝ)*(101/100) := by
    rw [hr,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply mul_le_mul _ hzabs (abs_nonneg _) (by norm_num)
    linarith
  refine ⟨by norm_num at hprod ⊢; linarith,?_⟩
  intro hgap
  have heupper : e ≤ 1/1000 := (le_abs_self e).trans he
  have hzlower : (99/100:ℝ) ≤ z := by have hh := (abs_le.mp hz).1; linarith
  have hxlower : (249/2000:ℝ) ≤ (g-e)/2 := by linarith
  have hmul := mul_le_mul hxlower hzlower (by norm_num : (0:ℝ) ≤ 99/100) (by linarith : 0 ≤ (g-e)/2)
  rw [hr]
  linarith

private lemma center_grid_one {N : ℕ} (hR : 2 ≤ Radius N) : Grid N (Center N) 1 := by
  refine ⟨by norm_num,by omega,by simp only [sub_self,abs_zero]; positivity,?_⟩
  unfold Center
  omega

private lemma grid_rectangle {N M l : ℕ} (h : Grid N M l) : Rectangle N M l :=
  ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,h.2.2.1⟩

private lemma gap_grid_data {N k w q : ℕ} (hN : 0 < N) (hR : 2 ≤ Radius N)
    (hq : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ)) (H : Bivariate)
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N 3) k w q)
    (out : (Address N 3 × Bits k) × Fin w → Bool)
    (hD : ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0)
    (hH : ∀ M l : ℕ, Grid N M l → FeasibleGap E A out M l =
      l*Eval H M l/Eval (Denominator q) M l+GapError E A out M l)
    (hErr : ∀ M l : ℕ, Grid N M l → |GapError E A out M l| ≤ 1/1000)
    (hcenter : (1/4:ℝ) ≤ FeasibleGap E A out (Center N) 1) :
    (∀ X l : ℤ, 1 ≤ l → l ≤ (Radius N:ℤ) →
      |(X:ℝ)-(Center N/2:ℕ)| ≤ (Radius N:ℝ)^(3/2:ℝ)/2 → l ∣ X →
        |Eval (ScaleFirst (GapPolynomial N q H)) X l| ≤ 1) ∧
    Eval (ScaleFirst (GapPolynomial N q H)) (Center N/2:ℕ) 0 = 0 ∧
    (1/10:ℝ) ≤ |Eval (ScaleFirst (GapPolynomial N q H)) (Center N/2:ℕ) 1| := by
  have hrec := reciprocal_bound N q hN hq
  have hlocal (M l : ℕ) (hg : Grid N M l) := approximate_gap_bounds
    (FeasibleGap E A out M l) (GapError E A out M l)
    (Eval (Denominator q) M l*Eval (ReciprocalPolynomial N q) M l)
    (Eval (GapPolynomial N q H) M l)
    (gap_polynomial_eval H E A out (hD M l hg) (hH M l hg))
    (feasible_gap_bound E A out M l) (hErr M l hg) (hrec.2 M l (grid_rectangle hg))
  refine ⟨?_,?_,?_⟩
  · intro X l hl hlR hwindow hdiv
    obtain ⟨hg,hxr,hlr⟩ := natural_grid hN hl hlR hwindow hdiv
    have hh := (hlocal (2*X.toNat) l.toNat hg).1
    rw [scale_first_eval]
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hxr,hlr] using hh
  · rw [scale_first_eval]
    simp [GapPolynomial,Eval]
  · have hh := (hlocal (Center N) 1 (center_grid_one hR)).2 hcenter
    have hce : (2:ℝ)*(Center N/2:ℕ) = Center N := by exact_mod_cast center_even N
    rw [scale_first_eval,hce]
    have hh' : (1/10:ℝ) ≤ Eval (GapPolynomial N q H) (Center N) 1 := by simpa only [Nat.cast_one] using hh
    exact hh'.trans (le_abs_self _)

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness
open Finset Filter
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

theorem solution : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ k w q : ℕ,
    ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      (1/4:ℝ) ≤ FeasibleGap E A out (Center N) 1 → c*LowerBoundScale N ≤ (q:ℝ) := by
  obtain ⟨C,c₀,hC,hc₀,hvan,hpoly,Nden,hden⟩ := proposition_3_13
  obtain ⟨α,hα,hgrid⟩ := zero_anchored_grid_degree (1/10) (by norm_num)
  let S := C+64
  have hS : 0 < S := by dsimp [S]; linarith
  let c := min c₀ (min 1 (α/(160*S)))
  have hc : 0 < c := by dsimp [c]; exact lt_min hc₀ (lt_min (by norm_num) (by positivity))
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c ≤ α/(160*S) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Nerr,herr⟩ := hvan (1/1000) (by norm_num)
  have hp : Tendsto (fun N : ℕ => (N:ℝ)^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hNs⟩ := eventually_atTop.mp (hp.eventually_ge_atTop (max 20 (80*(1+S)/α)))
  let N₀ := max (max (max Nden Nerr) Ns) (max 2 ⌈Real.exp 1⌉₊)
  refine ⟨c,hc,N₀,by dsimp [N₀]; omega,?_⟩
  intro N hN k w q E A out hcenter
  have hN2 : 2 ≤ N := by dsimp [N₀] at hN; omega
  have hNpos : 0 < N := by omega
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hNpos
  have hPowPos : (0:ℝ) < (N:ℝ)^(1/3:ℝ) := Real.rpow_pos_of_pos hNr _
  have hExp : Real.exp 1 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp 1⌉₊ ≤ N by dsimp [N₀] at hN; omega))
  have hlog1 : (1:ℝ) ≤ Real.log N := by
    calc
      _ = Real.log (Real.exp 1) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hExp
  have hlogpos : 0 < Real.log (N:ℝ) := by linarith
  have hscale : 0 < LowerBoundScale N := div_pos hPowPos hlogpos
  by_contra hn
  have hqlt : (q:ℝ) < c*LowerBoundScale N := lt_of_not_ge hn
  have hqsmall : (q:ℝ) ≤ c₀*LowerBoundScale N :=
    hqlt.le.trans (mul_le_mul_of_nonneg_right hcc₀ hscale.le)
  have hqroot : (q:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := by
    apply hqlt.le.trans
    unfold LowerBoundScale
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogpos).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hc1.trans hlog1) hPowPos.le
  obtain ⟨H,hHdeg,hH⟩ := hpoly N k w q E A out
  have hD : ∀ M l : ℕ, Grid N M l → Eval (Denominator q) M l ≠ 0 :=
    hden N (by dsimp [N₀] at hN; omega) q hqsmall
  have hE : ∀ M l : ℕ, Grid N M l → |GapError E A out M l| ≤ 1/1000 :=
    herr N (by dsimp [N₀] at hN; omega) k w q hqsmall E A out
  have hlarge := hNs N (by dsimp [N₀] at hN; omega)
  have hP20 : (20:ℝ) ≤ (N:ℝ)^(1/3:ℝ) := (le_max_left _ _).trans hlarge
  obtain ⟨hR,hroot⟩ := radius_lower N hNpos hP20
  have hCpos : 0 < Center N/2 := by
    have hcN : N ≤ Center N := by exact_mod_cast center_bound N
    omega
  have hdata := gap_grid_data hNpos hR hqroot H E A out hD
    (fun M l hg => hH M l hg (hD M l hg)) hE hcenter
  have hlower := hgrid (Center N/2) (Radius N) hCpos hR (ScaleFirst (GapPolynomial N q H))
    hdata.1 hdata.2.1 hdata.2.2
  have hdegNat : (ScaleFirst (GapPolynomial N q H)).totalDegree ≤
      1+H.totalDegree+(ReciprocalPolynomial N q).totalDegree :=
    (scale_first_degree _).trans (gap_polynomial_degree N q H)
  have hdeg : ((ScaleFirst (GapPolynomial N q H)).totalDegree:ℝ) ≤
      1+(H.totalDegree:ℝ)+(ReciprocalPolynomial N q).totalDegree := by exact_mod_cast hdegNat
  have hrecdeg : ((ReciprocalPolynomial N q).totalDegree:ℝ) ≤ 64*DegreeScale q :=
    (Nat.cast_le.mpr (reciprocal_bound N q hNpos hqroot).1).trans (degree_bound q)
  have hup : ((ScaleFirst (GapPolynomial N q H)).totalDegree:ℝ) ≤ 1+S*DegreeScale q := by
    dsimp only [S]
    nlinarith
  have hsu := mul_le_mul_of_nonneg_left (scale_upper hN2 hqroot) hS.le
  have hupper : ((ScaleFirst (GapPolynomial N q H)).totalDegree:ℝ) ≤ 1+S+2*S*q*Real.log N := by nlinarith
  have hK : 80*(1+S)/α ≤ (N:ℝ)^(1/3:ℝ) := (le_max_right _ _).trans hlarge
  have hfixed : 1+S ≤ α/80*(N:ℝ)^(1/3:ℝ) := by
    have hh := (div_le_iff₀ hα).mp hK
    nlinarith
  have hqlog : (q:ℝ)*Real.log N ≤ c*(N:ℝ)^(1/3:ℝ) := by
    apply (le_div_iff₀ hlogpos).mp
    simpa only [LowerBoundScale,mul_div_assoc] using hqlt.le
  have hcc : 2*S*c ≤ α/80 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 160*S)).mp hca
    nlinarith
  have htail : 2*S*q*Real.log N ≤ α/80*(N:ℝ)^(1/3:ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hqlog (by positivity : (0:ℝ) ≤ 2*S)
    have h₂ := mul_le_mul_of_nonneg_right hcc hPowPos.le
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left hroot hα.le
  nlinarith
end
