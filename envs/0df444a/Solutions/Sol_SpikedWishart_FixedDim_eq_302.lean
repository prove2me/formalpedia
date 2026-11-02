-- Prove2me | solution 1 for SpikedWishart.FixedDim.eq_302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T00:37:40.397336+00:00
-- url     : https://prove2.me/submissions/1eeaf87c-6225-4cdb-911a-1cc8448e9055

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

set_option autoImplicit false



namespace SpikedWishart.Separated.Lib
open Filter Topology MeasureTheory Matrix Polynomial
open Filter Topology MeasureTheory Matrix Complex ProbabilityTheory
open Filter Topology MeasureTheory Matrix Polynomial ProbabilityTheory Complex

-- ===== from W1a.lean =====
section

namespace Weyl

open Finset

/-- Absolute Vandermonde product `∏_{i<j} |v i - v j|`. -/
noncomputable def vdm {m : ℕ} (v : Fin m → ℝ) : ℝ := ∏ i : Fin m, ∏ j ∈ Ioi i, |v i - v j|

/-- `D_i = ∏_{l ≠ i} (μ_i - μ_l)`. -/
noncomputable def Dn {n : ℕ} (mu : Fin n → ℝ) (i : Fin n) : ℝ := ∏ l ∈ univ.erase i, (mu i - mu l)

/-- Dixon-Anderson weights `w_i = -∏_j (μ_i - λ_j) / D_i`. -/
noncomputable def wv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  -(∏ j, (mu i - la j)) / Dn mu i

/-- The corner entry `c = Σ λ - Σ μ`. -/
noncomputable def cv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : ℝ := ∑ j, la j - ∑ i, mu i

/-- Strict interlacing `λ_0 > μ_0 > λ_1 > ... > μ_{n-1} > λ_n`. -/
def Ilace {n : ℕ} (mu : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {la | ∀ i : Fin n, mu i < la (Fin.castSucc i) ∧ la (Fin.succ i) < mu i}

theorem Dn_ne_zero {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (i : Fin n) :
    Dn mu i ≠ 0 := by
  unfold Dn
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hl) (hmu h).symm)

theorem degree_prod_sub_lt {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : ∑ j, a j = ∑ j, b j) :
    (∏ j, (X - C (a j)) - ∏ j, (X - C (b j))).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub, sub_eq_zero]
  have hda : (∏ j, (X - C (a j))).natDegree = n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]; simp
  have hdb : (∏ j, (X - C (b j))).natDegree = n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]; simp
  rcases Nat.lt_or_ge (n + 1) m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
  rcases (show m = n ∨ m = n + 1 by omega) with rfl | rfl
  · have h1 := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (m + 1))) a (by simp)
    have h2 := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (m + 1))) b (by simp)
    simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h1 h2
    rw [h1, h2, hab]
  · have ma : (∏ j, (X - C (a j))).Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
    have mb : (∏ j, (X - C (b j))).Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
    have e1 := ma.coeff_natDegree
    have e2 := mb.coeff_natDegree
    rw [hda] at e1
    rw [hdb] at e2
    rw [e1, e2]

theorem degree_lagr_lt {n : ℕ} (mu w : Fin n → ℝ) :
    (-(∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)))).degree < (n : WithBot ℕ) := by
  rw [degree_neg]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro i _
  rw [C_mul']
  refine lt_of_le_of_lt (degree_smul_le _ _) ?_
  rw [degree_eq_natDegree (Polynomial.Monic.ne_zero
    (monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _))), natDegree_finset_prod_X_sub_C_eq_card]
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hn one_pos)

/-- (P): the Dixon-Anderson polynomial identity
`∏ (X - λ_j) = (X - c) ∏ (X - μ_i) - Σ_i w_i ∏_{l≠i} (X - μ_l)`. -/
theorem poly_id {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (la : Fin (n + 1) → ℝ) :
    ∏ j, (X - C (la j)) = (X - C (cv mu la)) * ∏ i, (X - C (mu i)) -
      ∑ i, C (wv mu la i) * ∏ l ∈ univ.erase i, (X - C (mu l)) := by
  set nu : Fin (n + 1) → ℝ := Fin.snoc mu (cv mu la) with hnu
  have hprod : ∏ j, (X - C (nu j)) = (X - C (cv mu la)) * ∏ i, (X - C (mu i)) := by
    rw [Fin.prod_univ_castSucc]
    simp only [hnu, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have hsum : ∑ j, la j = ∑ j, nu j := by
    simp only [hnu, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, cv]
    ring
  have key : ∏ j, (X - C (la j)) - ∏ j, (X - C (nu j)) =
      -(∑ i, C (wv mu la i) * ∏ l ∈ univ.erase i, (X - C (mu l))) := by
    refine eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin n))) (v := mu)
      hmu.injOn ?_ ?_ ?_
    · rw [card_univ, Fintype.card_fin]; exact degree_prod_sub_lt la nu hsum
    · rw [card_univ, Fintype.card_fin]; exact degree_lagr_lt mu _
    · intro i _
      have hz : eval (mu i) (∏ j, (X - C (nu j))) = 0 := by
        rw [eval_prod, Finset.prod_eq_zero (i := Fin.castSucc i) (mem_univ _)]
        simp [hnu]
      rw [eval_sub, hz, sub_zero, eval_neg, eval_finsetSum,
        Finset.sum_eq_single i]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        have hD := Dn_ne_zero hmu i
        rw [eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        unfold wv
        change _ = -(-(∏ j, (mu i - la j)) / Dn mu i * Dn mu i)
        field_simp
      · intro l _ hli
        rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (mem_erase.mpr ⟨Ne.symm hli, mem_univ _⟩)]
        · ring
        · simp
      · intro h; exact absurd (mem_univ i) h
  rw [← hprod]
  linear_combination key

theorem poly_id_eval {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (la : Fin (n + 1) → ℝ)
    (t : ℝ) :
    ∏ j, (t - la j) = (t - cv mu la) * ∏ i, (t - mu i) -
      ∑ i, wv mu la i * ∏ l ∈ univ.erase i, (t - mu l) := by
  have h := congrArg (eval t) (poly_id hmu la)
  simpa [eval_prod, eval_finsetSum] using h

/-- Sign of a product of nonzero reals. -/
theorem prod_eq_sign_mul_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ j ∈ s, f j = (-1) ^ #(s.filter (fun j => f j < 0)) * ∏ j ∈ s, |f j| := by
  classical
  have h : ∀ j, f j = if f j < 0 then -|f j| else |f j| := by
    intro j
    split_ifs with hj
    · rw [abs_of_neg hj, neg_neg]
    · rw [abs_of_nonneg (not_lt.mp hj)]
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_ite, Finset.prod_neg]
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun j => f j < 0) (f := fun j => |f j|)]
  ring

theorem ilace_strictAnti {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    StrictAnti la := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  exact lt_trans (h i).2 (h i).1

theorem ilace_mu_strictAnti {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    StrictAnti mu := by
  intro i j hij
  have ha := (ilace_strictAnti h).antitone
  have hle : Fin.succ i ≤ Fin.castSucc j := by
    rw [Fin.le_def]; simp; exact hij
  exact lt_of_lt_of_le (h j).1 (ha hle) |>.trans (h i).2

theorem filter_la {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    (univ.filter (fun j => mu i - la j < 0)) = Iic (Fin.castSucc i) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_Iic, sub_neg]
  have ha := (ilace_strictAnti h).antitone
  constructor
  · intro hj
    by_contra hc
    have : Fin.succ i ≤ j := by
      rw [not_le, Fin.lt_def] at hc; rw [Fin.le_def]; simp at hc ⊢; omega
    exact absurd (lt_trans (lt_of_le_of_lt (ha this) (h i).2) hj) (lt_irrefl _)
  · intro hj
    exact lt_of_lt_of_le (h i).1 (ha hj)

theorem filter_mu {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    ((univ.erase i).filter (fun l => mu i - mu l < 0)) = Iio i := by
  ext l
  simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio, sub_neg]
  have hm := ilace_mu_strictAnti h
  constructor
  · rintro ⟨hne, hl⟩
    by_contra hc
    rcases lt_or_eq_of_le (not_lt.mp hc) with h' | h'
    · exact absurd (lt_trans hl (hm h')) (lt_irrefl _)
    · exact hne h'.symm
  · intro hl
    exact ⟨ne_of_lt hl, hm hl⟩

theorem wv_pos {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    0 < wv mu la i := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  have hla : Function.Injective la := (ilace_strictAnti h).injective
  unfold wv Dn
  rw [prod_eq_sign_mul_abs, prod_eq_sign_mul_abs (univ.erase i), filter_la h, filter_mu h,
    Fin.card_Iic, Fin.card_Iio, Fin.val_castSucc]
  have hA : 0 < ∏ j, |mu i - la j| := by
    apply Finset.prod_pos; intro j _
    apply abs_pos.mpr
    intro he
    have : mu i = la j := sub_eq_zero.mp he
    rcases lt_or_ge j (Fin.succ i) with hj | hj
    · have hj' : j ≤ Fin.castSucc i := by rw [Fin.le_def]; rw [Fin.lt_def] at hj; simp at hj ⊢; omega
      exact absurd (this ▸ lt_of_lt_of_le (h i).1 ((ilace_strictAnti h).antitone hj')) (lt_irrefl _)
    · exact absurd (this ▸ lt_of_le_of_lt ((ilace_strictAnti h).antitone hj) (h i).2) (lt_irrefl _)
  have hB : 0 < ∏ l ∈ univ.erase i, |mu i - mu l| := by
    apply Finset.prod_pos; intro l hl
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => (ne_of_mem_erase hl) (hmu he).symm))
  have hs : ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_succ]
  have : -((-1 : ℝ) ^ (i : ℕ) * -1 * ∏ j, |mu i - la j|) / ((-1) ^ (i : ℕ) * ∏ l ∈ univ.erase i, |mu i - mu l|)
      = (∏ j, |mu i - la j|) / ∏ l ∈ univ.erase i, |mu i - mu l| := by
    have hne : ((-1 : ℝ) ^ (i : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [this]
  exact div_pos hA hB

theorem vdm_eq_abs_det {m : ℕ} (v : Fin m → ℝ) : vdm v = |(vandermonde v).det| := by
  rw [det_vandermonde, vdm, Finset.abs_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl (fun j _ => abs_sub_comm _ _)

end Weyl

end

-- ===== from W1b.lean =====
section

namespace Weyl

open Finset

/-- `∏_{j} ∏_{k ≠ j} |v j - v k| = vdm v ^ 2`. -/
theorem prod_offdiag_abs {m : ℕ} (v : Fin m → ℝ) :
    ∏ j, ∏ k ∈ univ.erase j, |v j - v k| = vdm v ^ 2 := by
  have hsplit : ∀ j : Fin m, univ.erase j = Iio j ∪ Ioi j := by
    intro j; ext k
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : ∀ j : Fin m, Disjoint (Iio j) (Ioi j) := by
    intro j; rw [Finset.disjoint_left]; intro k h1 h2; simp at h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  simp_rw [hsplit, Finset.prod_union (hdisj _), Finset.prod_mul_distrib]
  have hcomm : ∏ j : Fin m, ∏ k ∈ Iio j, |v j - v k| = ∏ k : Fin m, ∏ j ∈ Ioi k, |v j - v k| :=
    Finset.prod_comm' (fun j k => by simp)
  rw [hcomm, vdm, sq]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => Finset.prod_congr rfl (fun j _ => abs_sub_comm _ _))

theorem vdm_pos {m : ℕ} {v : Fin m → ℝ} (hv : Function.Injective v) : 0 < vdm v := by
  unfold vdm
  apply Finset.prod_pos; intro i _; apply Finset.prod_pos; intro j hj
  exact abs_pos.mpr (sub_ne_zero.mpr (fun h => (ne_of_lt (mem_Ioi.mp hj)) (hv h)))

theorem prod_abs_Dn {n : ℕ} (mu : Fin n → ℝ) : ∏ i, |Dn mu i| = vdm mu ^ 2 := by
  rw [← prod_offdiag_abs]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Dn, Finset.abs_prod]

/-- `q_j = ∏_{k ≠ j} (X - λ_k)`. -/
noncomputable def qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ[X] :=
  ∏ k ∈ univ.erase j, (X - C (la k))

theorem qp_monic {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : (qp la j).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem qp_natDegree {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : (qp la j).natDegree = n := by
  rw [qp, natDegree_finsetProd_X_sub_C_eq_card, card_erase_of_mem (mem_univ j), card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]

theorem eval_qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (t : ℝ) :
    (qp la j).eval t = ∏ k ∈ univ.erase j, (t - la k) := by
  rw [qp, eval_prod]; simp

theorem sum_coeff_qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (t : ℝ) :
    ∑ m : Fin (n + 1), t ^ (m : ℕ) * (qp la j).coeff m = (qp la j).eval t := by
  rw [eval_eq_sum_range' (n := n + 1) (by rw [qp_natDegree]; omega)]
  rw [Fin.sum_univ_eq_sum_range (fun m => t ^ m * (qp la j).coeff m) (n + 1)]
  exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)

/-- Coefficient matrix `Cm m j = coeff_m q_j`. -/
noncomputable def Cm {n : ℕ} (la : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun m j => (qp la j).coeff m

theorem vandermonde_mul_Cm {n : ℕ} (la : Fin (n + 1) → ℝ) :
    vandermonde la * Cm la = diagonal (fun j => ∏ k ∈ univ.erase j, (la j - la k)) := by
  ext k j
  rw [mul_apply]
  simp only [vandermonde_apply, Cm, Matrix.of_apply]
  rw [sum_coeff_qp, eval_qp, diagonal_apply]
  split_ifs with h
  · subst h; rfl
  · exact Finset.prod_eq_zero (i := k) (mem_erase.mpr ⟨h, mem_univ _⟩) (sub_self _)

theorem abs_det_Cm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : Function.Injective la) :
    |(Cm la).det| = vdm la := by
  have h := congrArg (fun A => |det A|) (vandermonde_mul_Cm la)
  simp only [det_mul, abs_mul, det_diagonal, Finset.abs_prod] at h
  rw [← vdm_eq_abs_det, prod_offdiag_abs, sq] at h
  have hp := vdm_pos hla
  exact mul_left_cancel₀ hp.ne' h

/-- `B`: Vandermonde rows of `μ` plus the last unit row. -/
noncomputable def Bm {n : ℕ} (mu : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i m => Fin.snoc (α := fun _ => ℝ) (fun i' => mu i' ^ (m : ℕ))
    (if m = Fin.last n then 1 else 0) i

theorem det_Bm {n : ℕ} (mu : Fin n → ℝ) : (Bm mu).det = (vandermonde mu).det := by
  rw [det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp only [Bm, Matrix.of_apply, Fin.snoc_last, if_pos rfl, Fin.succAbove_last]
    have : (Bm mu).submatrix Fin.castSucc Fin.castSucc = vandermonde mu := by
      ext i m; simp [Bm, vandermonde_apply]
    simp only [Bm] at this
    rw [this]
    simp [← pow_add, ← two_mul, pow_mul]
  · intro j _ hj
    simp [Bm, hj]
  · intro h; exact absurd (mem_univ _) h

/-- `A i j = q_j(μ_i)` for `i < n`, last row `1`. -/
noncomputable def Am {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.snoc (α := fun _ => ℝ) (fun i' => ∏ k ∈ univ.erase j, (mu i' - la k)) 1 i

theorem Bm_mul_Cm {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : Bm mu * Cm la = Am mu la := by
  ext i j
  rw [mul_apply]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [Bm, Am, Cm, Matrix.of_apply, Fin.snoc_last, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', mem_univ, if_true]
    have := (qp_monic la j).coeff_natDegree
    rw [qp_natDegree] at this
    simpa using this
  · simp only [Bm, Am, Cm, Matrix.of_apply, Fin.snoc_castSucc]
    rw [sum_coeff_qp, eval_qp]

/-- The Jacobian matrix of `λ ↦ (w(λ), c(λ))`. -/
noncomputable def Jm {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.snoc (α := fun _ => ℝ)
    (fun i' => (∏ k ∈ univ.erase j, (mu i' - la k)) / Dn mu i') 1 i

theorem Jm_eq {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Jm mu la = diagonal (Fin.snoc (α := fun _ => ℝ) (fun i' => (Dn mu i')⁻¹) 1) * Am mu la := by
  ext i j
  rw [diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [Jm, Am]
  · simp only [Jm, Am, Matrix.of_apply, Fin.snoc_castSucc]
    rw [div_eq_inv_mul]

theorem abs_det_Jm {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (hmu : Function.Injective mu)
    (hla : Function.Injective la) : |(Jm mu la).det| = vdm la / vdm mu := by
  rw [Jm_eq, det_mul, det_diagonal, ← Bm_mul_Cm, det_mul, det_Bm, abs_mul, abs_mul,
    abs_det_Cm hla, ← vdm_eq_abs_det, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one, Finset.abs_prod, abs_inv]
  rw [Finset.prod_inv_distrib, prod_abs_Dn]
  have hp := vdm_pos hmu
  field_simp

end Weyl

end

-- ===== from W1c.lean =====
section

namespace Weyl

open Finset

/-- The real arrow matrix `[[diag μ, b], [bᵀ, c]]` on `Fin (n+1)`. -/
noncomputable def arrowR {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (diagonal mu) (Matrix.of fun i (_ : Fin 1) => b i) (Matrix.of fun (_ : Fin 1) j => b j)
      (Matrix.of fun _ _ => c))

theorem arrowR_cc {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i j : Fin n) :
    arrowR mu b c (Fin.castSucc i) (Fin.castSucc j) = diagonal mu i j := by
  simp [arrowR, reindex_apply]

theorem arrowR_cl {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    arrowR mu b c (Fin.castSucc i) (Fin.last n) = b i := by
  simp [arrowR, reindex_apply]

theorem arrowR_lc {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    arrowR mu b c (Fin.last n) (Fin.castSucc j) = b j := by
  simp [arrowR, reindex_apply]

theorem arrowR_ll {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) :
    arrowR mu b c (Fin.last n) (Fin.last n) = c := by
  simp [arrowR, reindex_apply]

theorem arrowR_symm {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i j : Fin (n + 1)) :
    arrowR mu b c i j = arrowR mu b c j i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · rfl
  · rw [arrowR_lc, arrowR_cl]
  · rw [arrowR_lc, arrowR_cl]
  · rw [arrowR_cc, arrowR_cc, diagonal_apply, diagonal_apply]
    by_cases h : i' = j'
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem charpoly_arrowR_eval {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (t : ℝ) (ht : ∀ i, t ≠ mu i) :
    (arrowR mu b c).charpoly.eval t = (∏ i, (t - mu i)) * ((t - c) - ∑ i, b i ^ 2 / (t - mu i)) := by
  rw [arrowR, charpoly_reindex, eval_charpoly]
  have hsc : (scalar (Fin n ⊕ Fin 1) t : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) =
      fromBlocks (diagonal fun _ => t) 0 0 (diagonal fun _ => t) := by
    rw [scalar_apply, fromBlocks_diagonal]; congr 1; ext x; cases x <;> rfl
  rw [hsc, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  set A : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => t - mu i) with hA
  have hA' : diagonal (fun _ => t) + -diagonal mu = A := by
    rw [hA, ← sub_eq_add_neg, diagonal_sub]
  rw [hA']
  have hinv : diagonal (fun i => (t - mu i)⁻¹) * A = 1 := by
    rw [hA, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; exact inv_mul_cancel₀ (sub_ne_zero.mpr (ht i))
  letI : Invertible A := invertibleOfLeftInverse A _ hinv
  have hdetA : A.det = ∏ i, (t - mu i) := by rw [hA, det_diagonal]
  rw [det_fromBlocks₁₁, hdetA, det_unique]
  congr 1
  show _ = t - c - ∑ i, b i ^ 2 / (t - mu i)
  have hinvOf : (⅟A : Matrix (Fin n) (Fin n) ℝ) = diagonal (fun i => (t - mu i)⁻¹) := rfl
  rw [hinvOf]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, mul_apply, diagonal_apply,
    Matrix.zero_apply, mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
  rw [← sub_eq_add_neg t c]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- With `b = √w(λ)`, `c = c(λ)`, the arrow matrix has characteristic polynomial `∏ (X - λ_j)`. -/
theorem charpoly_arrowR {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    (arrowR mu (fun i => Real.sqrt (wv mu la i)) (cv mu la)).charpoly = ∏ j, (X - C (la j)) := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  apply eq_of_infinite_eval_eq
  have hinf : (Set.range mu)ᶜ.Infinite := (Set.finite_range mu).infinite_compl
  refine hinf.mono (fun t ht => ?_)
  have ht' : ∀ i, t ≠ mu i := fun i he => ht ⟨i, he.symm⟩
  show _ = _
  rw [charpoly_arrowR_eval _ _ _ _ ht']
  have hw : ∀ i, Real.sqrt (wv mu la i) ^ 2 = wv mu la i := fun i => Real.sq_sqrt (wv_pos h i).le
  simp only [hw]
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [poly_id_eval hmu la t, mul_sub, mul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_prod_erase univ (fun l => t - mu l) (mem_univ i)]
  have : t - mu i ≠ 0 := sub_ne_zero.mpr (ht' i)
  field_simp

/-- The complex arrow matrix. -/
noncomputable def arrowC {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (arrowR mu b c).map (fun x : ℝ => (x : ℂ))

theorem arrowC_isHermitian {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : (arrowC mu b c).IsHermitian := by
  ext i j
  simp [arrowC, conjTranspose_apply, arrowR_symm mu b c i j]

theorem perm_conj_diag {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    diagonal (d ∘ σ) = (1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id * diagonal d *
      star ((1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id) := by
  ext i j
  simp only [mul_apply, diagonal_apply, submatrix_apply, one_apply, id, star_apply, Function.comp_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, σ.injective.eq_iff]
  split_ifs with h <;> simp [h]

theorem perm_mem_unitary {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id ∈ unitaryGroup (Fin m) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j
  simp only [mul_apply, submatrix_apply, one_apply, id, star_apply]
  simp [Finset.sum_ite_eq', σ.injective.eq_iff]

/-- (K) The arrow matrix with `b = √w(λ)`, `c = c(λ)` is unitarily similar to `diag λ`. -/
theorem arrowC_similar {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    ∃ U ∈ unitaryGroup (Fin (n + 1)) ℂ,
      arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) =
        U * diagonal (fun j => (la j : ℂ)) * star U := by
  set A := arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) with hAdef
  have hA : A.IsHermitian := arrowC_isHermitian _ _ _
  have hla : Function.Injective la := (ilace_strictAnti h).injective
  -- roots of the characteristic polynomial
  have hcp : A.charpoly = ∏ j, (X - C ((la j : ℝ) : ℂ)) := by
    have hf : (fun x : ℝ => (x : ℂ)) = ⇑Complex.ofRealHom := rfl
    rw [hAdef, arrowC, hf, charpoly_map, charpoly_arrowR h, Polynomial.map_prod]
    simp
  have hroots : Multiset.map (fun j => ((la j : ℝ) : ℂ)) univ.val =
      Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) univ.val := by
    rw [← hA.roots_charpoly_eq_eigenvalues, hcp, Finset.prod_eq_multiset_prod,
      show (fun j => X - C ((la j : ℝ) : ℂ)) = (fun a => X - C a) ∘ (fun j => ((la j : ℝ) : ℂ)) from rfl,
      ← Multiset.map_map (fun a => X - C a) (fun j => ((la j : ℝ) : ℂ)), roots_multiset_prod_X_sub_C]
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map] at hre
  have hev : Multiset.map la univ.val = Multiset.map hA.eigenvalues univ.val := by
    simpa [Function.comp_def] using hre
  have hnd : (Multiset.map hA.eigenvalues univ.val).Nodup := by
    rw [← hev]; exact (Multiset.nodup_map_iff_inj_on univ.nodup).mpr (fun x _ y _ hxy => hla hxy)
  have hevinj : Function.Injective hA.eigenvalues := by
    intro x y hxy
    exact (Multiset.nodup_map_iff_inj_on univ.nodup).mp hnd x (Finset.mem_val.mpr (mem_univ _)) y
      (Finset.mem_val.mpr (mem_univ _)) hxy
  have hmem : ∀ i, ∃ j, la j = hA.eigenvalues i := by
    intro i
    have : hA.eigenvalues i ∈ Multiset.map la univ.val := by
      rw [hev]; exact Multiset.mem_map_of_mem _ (mem_univ i)
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp this
    exact ⟨j, hj⟩
  choose s hs using hmem
  have hsinj : Function.Injective s := by
    intro x y hxy; apply hevinj; rw [← hs x, ← hs y, hxy]
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj)
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix σ id
  have hd : (RCLike.ofReal ∘ hA.eigenvalues : Fin (n + 1) → ℂ) = (fun j => ((la j : ℝ) : ℂ)) ∘ σ := by
    ext i; simp [σ, hs]
  refine ⟨(hA.eigenvectorUnitary).1 * P, Submonoid.mul_mem _ hA.eigenvectorUnitary.2 (perm_mem_unitary σ), ?_⟩
  conv_lhs => rw [hspec]
  rw [hd, perm_conj_diag, star_mul]
  simp only [mul_assoc]
  rfl

end Weyl

end

-- ===== from W1d.lean =====
section

namespace Weyl

open Finset

/-- The secular function `t - c - Σ w_i / (t - μ_i)`. -/
noncomputable def sec {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) : ℝ := t - c - ∑ i, w i / (t - mu i)

/-- The Dixon-Anderson map `λ ↦ (w(λ), c(λ))`. -/
noncomputable def Phi {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (wv mu la) (cv mu la)

/-- Target set `{y | y_i > 0 for i < n}`. -/
def Vpos (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | ∀ i : Fin n, 0 < y (Fin.castSucc i)}

/-- `R(t) = (t - c) ∏ (t - μ_i) - Σ w_i ∏_{l ≠ i} (t - μ_l)`. -/
noncomputable def Rf {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) : ℝ :=
  (t - c) * ∏ i, (t - mu i) - ∑ i, w i * ∏ l ∈ univ.erase i, (t - mu l)

theorem Rf_eq_prod_sec {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) (ht : ∀ i, t ≠ mu i) :
    Rf mu w c t = (∏ i, (t - mu i)) * sec mu w c t := by
  have key : ∀ i, (∏ l, (t - mu l)) * (w i / (t - mu i)) = w i * ∏ l ∈ univ.erase i, (t - mu l) := by
    intro i
    rw [← Finset.mul_prod_erase univ (fun l => t - mu l) (mem_univ i)]
    have : t - mu i ≠ 0 := sub_ne_zero.mpr (ht i)
    field_simp
  unfold Rf sec
  rw [mul_sub, mul_sub, Finset.mul_sum]
  simp_rw [key]
  ring

theorem Rf_at_mu {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    Rf mu w c (mu i) = -(w i * Dn mu i) := by
  unfold Rf Dn
  rw [Finset.prod_eq_zero (i := i) (mem_univ _) (sub_self _), mul_zero, zero_sub,
    Finset.sum_eq_single i]
  · intro l _ hli
    rw [Finset.prod_eq_zero (i := i) (mem_erase.mpr ⟨Ne.symm hli, mem_univ _⟩) (sub_self _), mul_zero]
  · intro h; exact absurd (mem_univ i) h

theorem side_iff {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n)
    (j : Fin (n + 1)) : mu i < la j ↔ j ≤ Fin.castSucc i := by
  have := congrArg (fun s => j ∈ s) (filter_la h i)
  simp only [mem_filter, mem_univ, true_and, mem_Iic, sub_neg, eq_iff_iff] at this
  exact this

theorem la_ne_mu {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n)
    (j : Fin (n + 1)) : la j ≠ mu i := by
  intro he
  have ha := (ilace_strictAnti h).antitone
  rcases le_or_gt j (Fin.castSucc i) with hj | hj
  · exact absurd (he ▸ lt_of_lt_of_le (h i).1 (ha hj)) (lt_irrefl _)
  · have : Fin.succ i ≤ j := by rw [Fin.le_def]; rw [Fin.lt_def] at hj; simp at hj ⊢; omega
    exact absurd (he ▸ lt_of_le_of_lt (ha this) (h i).2) (lt_irrefl _)

theorem sec_root {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (j : Fin (n + 1)) :
    sec mu (wv mu la) (cv mu la) (la j) = 0 := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  have hne : ∀ i, la j ≠ mu i := fun i => la_ne_mu h i j
  have hR : Rf mu (wv mu la) (cv mu la) (la j) = 0 := by
    have := poly_id_eval hmu la (la j)
    rw [Finset.prod_eq_zero (i := j) (mem_univ _) (sub_self _)] at this
    unfold Rf; linarith
  rw [Rf_eq_prod_sec _ _ _ _ hne] at hR
  have hp : (∏ i, (la j - mu i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hne i))
  exact (mul_eq_zero.mp hR).resolve_left hp

theorem sec_lt {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℝ) {s t : ℝ} (hst : s < t)
    (hside : ∀ i, (mu i < s ↔ mu i < t)) (hs : ∀ i, s ≠ mu i) (ht : ∀ i, t ≠ mu i) :
    sec mu w c s < sec mu w c t := by
  unfold sec
  have key : ∀ i, w i / (t - mu i) ≤ w i / (s - mu i) := by
    intro i
    by_cases hi : mu i < s
    · have h1 : 0 < s - mu i := by linarith
      have h2 : 0 < t - mu i := by linarith
      exact div_le_div_of_nonneg_left (hw i) h1 (by linarith)
    · have hs' : s < mu i := lt_of_le_of_ne (not_lt.mp hi) (hs i)
      have ht' : t < mu i := lt_of_le_of_ne (not_lt.mp (fun h => hi ((hside i).mpr h))) (ht i)
      have hp : 0 < (t - mu i) * (s - mu i) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have h1 : s - mu i ≠ 0 := by linarith
      have h2 : t - mu i ≠ 0 := by linarith
      have e : w i / (s - mu i) - w i / (t - mu i) = w i * (t - s) / ((t - mu i) * (s - mu i)) := by
        field_simp; ring
      have : 0 ≤ w i * (t - s) / ((t - mu i) * (s - mu i)) :=
        div_nonneg (mul_nonneg (hw i) (by linarith)) hp.le
      linarith
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  linarith

theorem phi_injOn {n : ℕ} (mu : Fin n → ℝ) : Set.InjOn (Phi mu) (Ilace mu) := by
  intro la ha la' ha' hP
  have hw : wv mu la = wv mu la' := by
    funext i
    have := congrFun hP (Fin.castSucc i)
    simpa [Phi] using this
  have hc : cv mu la = cv mu la' := by
    have := congrFun hP (Fin.last n)
    simpa [Phi] using this
  have hwpos : ∀ i, 0 ≤ wv mu la i := fun i => (wv_pos ha i).le
  funext j
  by_contra hne
  have hside : ∀ i, (mu i < la j ↔ mu i < la' j) := by
    intro i; rw [side_iff ha, side_iff ha']
  have r1 := sec_root ha j
  have r2 := sec_root ha' j
  rw [← hw, ← hc] at r2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := sec_lt mu _ hwpos (cv mu la) hlt hside (fun i => la_ne_mu ha i j) (fun i => la_ne_mu ha' i j)
    linarith
  · have := sec_lt mu _ hwpos (cv mu la) hlt (fun i => (hside i).symm) (fun i => la_ne_mu ha' i j)
      (fun i => la_ne_mu ha i j)
    linarith

/-- The interval of the `j`-th root. -/
def Jset {n : ℕ} (mu : Fin n → ℝ) (j : Fin (n + 1)) : Set ℝ :=
  {t | ∀ i : Fin n, (j ≤ Fin.castSucc i → mu i < t) ∧ (¬ j ≤ Fin.castSucc i → t < mu i)}

theorem Jset_ordConnected {n : ℕ} (mu : Fin n → ℝ) (j : Fin (n + 1)) : (Jset mu j).OrdConnected := by
  refine ⟨fun a ha b hb x hx => ?_⟩
  intro i
  exact ⟨fun h => lt_of_lt_of_le ((ha i).1 h) hx.1, fun h => lt_of_le_of_lt hx.2 ((hb i).2 h)⟩

theorem Jset_ne {n : ℕ} {mu : Fin n → ℝ} {j : Fin (n + 1)} {t : ℝ} (ht : t ∈ Jset mu j) (i : Fin n) :
    t ≠ mu i := by
  by_cases h : j ≤ Fin.castSucc i
  · exact ne_of_gt ((ht i).1 h)
  · exact ne_of_lt ((ht i).2 h)

theorem sec_continuousOn {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (j : Fin (n + 1)) :
    ContinuousOn (sec mu w c) (Jset mu j) := by
  unfold sec
  refine (continuousOn_id.sub continuousOn_const).sub (continuousOn_finsetSum _ (fun i _ => ?_))
  exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    (fun t ht => sub_ne_zero.mpr (Jset_ne ht i))

theorem sum_abs_ge {n : ℕ} (mu : Fin n → ℝ) (i : Fin n) : |mu i| ≤ ∑ l, |mu l| :=
  Finset.single_le_sum (f := fun l => |mu l|) (fun l _ => abs_nonneg _) (mem_univ i)

/-- Far to the left the secular function is negative. -/
theorem sec_neg_far {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    let t0 := -(|c| + ∑ i, w i + ∑ i, |mu i| + 2)
    (∀ i, t0 < mu i) ∧ sec mu w c t0 < 0 := by
  intro t0
  have hwn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hlt : ∀ i, t0 - mu i < -1 := by
    intro i
    have := sum_abs_ge mu i
    have := neg_abs_le (mu i)
    have := abs_nonneg c
    simp only [t0]; linarith
  refine ⟨fun i => by linarith [hlt i], ?_⟩
  have key : ∀ i, -w i ≤ w i / (t0 - mu i) := by
    intro i
    have hn : t0 - mu i < 0 := by linarith [hlt i]
    rw [le_div_iff_of_neg hn]
    nlinarith [hw i, hlt i]
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  rw [Finset.sum_neg_distrib] at this
  unfold sec
  have := le_abs_self c
  have := neg_abs_le c
  have hs : 0 ≤ ∑ i, |mu i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  simp only [t0] at this ⊢
  linarith

/-- Far to the right the secular function is positive. -/
theorem sec_pos_far {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    let t0 := |c| + ∑ i, w i + ∑ i, |mu i| + 2
    (∀ i, mu i < t0) ∧ 0 < sec mu w c t0 := by
  intro t0
  have hwn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hgt : ∀ i, 1 < t0 - mu i := by
    intro i
    have := sum_abs_ge mu i
    have := le_abs_self (mu i)
    have := abs_nonneg c
    simp only [t0]; linarith
  refine ⟨fun i => by linarith [hgt i], ?_⟩
  have key : ∀ i, w i / (t0 - mu i) ≤ w i := by
    intro i
    have hp : 0 < t0 - mu i := by linarith [hgt i]
    rw [div_le_iff₀ hp]
    nlinarith [hw i, hgt i]
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  unfold sec
  have := le_abs_self c
  have hs : 0 ≤ ∑ i, |mu i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  simp only [t0] at this ⊢
  linarith

theorem sec_split {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (i0 : Fin n) (t : ℝ) :
    sec mu w c t = (t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) + -(w i0 * (t - mu i0)⁻¹) := by
  unfold sec
  rw [← Finset.add_sum_erase univ _ (mem_univ i0), div_eq_mul_inv]
  ring

theorem cont_rest {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (c : ℝ) (i0 : Fin n) :
    ContinuousAt (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (mu i0) := by
  refine (continuousAt_id.sub continuousAt_const).sub ?_
  refine tendsto_finset_sum _ (fun i hi => ?_)
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (sub_ne_zero.mpr (fun h => (ne_of_mem_erase hi) (hmu h).symm))

theorem sec_atBot {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (hw : ∀ i, 0 < w i)
    (c : ℝ) (i0 : Fin n) : Tendsto (sec mu w c) (𝓝[>] (mu i0)) atBot := by
  have h1 : Tendsto (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (𝓝[>] (mu i0))
      (𝓝 (mu i0 - c - ∑ i ∈ univ.erase i0, w i / (mu i0 - mu i))) :=
    (cont_rest mu w hmu c i0).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => t - mu i0) (𝓝[>] (mu i0)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t => t - mu i0) (𝓝 (mu i0)) (𝓝 (mu i0 - mu i0)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (Set.mem_Ioi.mp ht)
  have h3 : Tendsto (fun t => (t - mu i0)⁻¹) (𝓝[>] (mu i0)) atTop := tendsto_inv_nhdsGT_zero.comp h2
  have h4 : Tendsto (fun t => -(w i0 * (t - mu i0)⁻¹)) (𝓝[>] (mu i0)) atBot :=
    tendsto_neg_atTop_atBot.comp (h3.const_mul_atTop (hw i0))
  have := h1.add_atBot h4
  refine this.congr (fun t => (sec_split mu w c i0 t).symm)

theorem sec_atTop {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (hw : ∀ i, 0 < w i)
    (c : ℝ) (i0 : Fin n) : Tendsto (sec mu w c) (𝓝[<] (mu i0)) atTop := by
  have h1 : Tendsto (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (𝓝[<] (mu i0))
      (𝓝 (mu i0 - c - ∑ i ∈ univ.erase i0, w i / (mu i0 - mu i))) :=
    (cont_rest mu w hmu c i0).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => t - mu i0) (𝓝[<] (mu i0)) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t => t - mu i0) (𝓝 (mu i0)) (𝓝 (mu i0 - mu i0)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_neg.mpr (Set.mem_Iio.mp ht)
  have h3 : Tendsto (fun t => (t - mu i0)⁻¹) (𝓝[<] (mu i0)) atBot := tendsto_inv_nhdsLT_zero.comp h2
  have h4 : Tendsto (fun t => -(w i0 * (t - mu i0)⁻¹)) (𝓝[<] (mu i0)) atTop :=
    tendsto_neg_atBot_atTop.comp (h3.const_mul_atBot (hw i0))
  have := h1.add_atTop h4
  refine this.congr (fun t => (sec_split mu w c i0 t).symm)

theorem exists_neg {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ a ∈ Jset mu j, sec mu w c a < 0 := by
  refine Fin.lastCases ?_ (fun i0 => ?_) j
  · obtain ⟨h1, h2⟩ := sec_neg_far mu w hw c
    refine ⟨_, fun i => ⟨fun h => absurd h ?_, fun _ => h1 i⟩, h2⟩
    rw [not_le, Fin.lt_def]; simp
  · have hev : ∀ᶠ t in 𝓝[>] (mu i0), t ∈ Jset mu (Fin.castSucc i0) := by
      have : ∀ i, ∀ᶠ t in 𝓝[>] (mu i0), (Fin.castSucc i0 ≤ Fin.castSucc i → mu i < t) ∧
          (¬ Fin.castSucc i0 ≤ Fin.castSucc i → t < mu i) := by
        intro i
        by_cases hi : Fin.castSucc i0 ≤ Fin.castSucc i
        · have hle : mu i ≤ mu i0 := hmu.antitone (Fin.castSucc_le_castSucc_iff.mp hi)
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact ⟨fun _ => lt_of_le_of_lt hle ht, fun h => absurd hi h⟩
        · have hlt : mu i0 < mu i := hmu (by rw [Fin.castSucc_le_castSucc_iff, not_le] at hi; exact hi)
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with t ht
          exact ⟨fun h => absurd h hi, fun _ => ht⟩
      exact Filter.eventually_all.mpr this
    have hneg := (sec_atBot mu w hmu.injective hw c i0).eventually (eventually_lt_atBot 0)
    obtain ⟨t, ht1, ht2⟩ := (hev.and hneg).exists
    exact ⟨t, ht1, ht2⟩

theorem exists_pos {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ b ∈ Jset mu j, 0 < sec mu w c b := by
  refine Fin.cases ?_ (fun i0 => ?_) j
  · obtain ⟨h1, h2⟩ := sec_pos_far mu w hw c
    refine ⟨_, fun i => ⟨fun _ => h1 i, fun h => absurd (Fin.zero_le _) h⟩, h2⟩
  · have hev : ∀ᶠ t in 𝓝[<] (mu i0), t ∈ Jset mu (Fin.succ i0) := by
      have : ∀ i, ∀ᶠ t in 𝓝[<] (mu i0), (Fin.succ i0 ≤ Fin.castSucc i → mu i < t) ∧
          (¬ Fin.succ i0 ≤ Fin.castSucc i → t < mu i) := by
        intro i
        by_cases hi : Fin.succ i0 ≤ Fin.castSucc i
        · have hlt : mu i < mu i0 := hmu (by rw [Fin.le_def] at hi; rw [Fin.lt_def]; simp at hi; omega)
          filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with t ht
          exact ⟨fun _ => ht, fun h => absurd hi h⟩
        · have hle : mu i0 ≤ mu i := hmu.antitone (by
            rw [Fin.le_def] at hi ⊢; simp at hi; omega)
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact ⟨fun h => absurd h hi, fun _ => lt_of_lt_of_le ht hle⟩
      exact Filter.eventually_all.mpr this
    have hpos := (sec_atTop mu w hmu.injective hw c i0).eventually (eventually_gt_atTop 0)
    obtain ⟨t, ht1, ht2⟩ := (hev.and hpos).exists
    exact ⟨t, ht1, ht2⟩

theorem exists_root {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ t ∈ Jset mu j, sec mu w c t = 0 := by
  obtain ⟨a, ha, hfa⟩ := exists_neg hmu w hw c j
  obtain ⟨b, hb, hfb⟩ := exists_pos hmu w hw c j
  have := (Jset_ordConnected mu j).isPreconnected.intermediate_value ha hb (sec_continuousOn mu w c j)
  obtain ⟨t, ht, hft⟩ := this ⟨hfa.le, hfb.le⟩
  exact ⟨t, ht, hft⟩

theorem degree_R_sub_lt {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (la : Fin (n + 1) → ℝ) :
    ((X - C c) * ∏ i, (X - C (mu i)) - ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)) -
      ∏ j, (X - C (la j))).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  set nu : Fin (n + 1) → ℝ := Fin.snoc mu c with hnu
  have hprod : ∏ j, (X - C (nu j)) = (X - C c) * ∏ i, (X - C (mu i)) := by
    rw [Fin.prod_univ_castSucc]
    simp only [hnu, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have hA : (∏ j, (X - C (nu j)) - ∏ j, (X - C (la j))).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have m1 : (∏ j, (X - C (nu j))).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have m2 : (∏ j, (X - C (la j))).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have d1 : (∏ j, (X - C (nu j))).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree m1.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
    have d2 : (∏ j, (X - C (la j))).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree m2.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
    rw [← d1]
    exact degree_sub_lt_left (d1.trans d2.symm) m1.ne_zero (by rw [m1.leadingCoeff, m2.leadingCoeff])
  have hL := degree_lagr_lt mu w
  rw [degree_neg] at hL
  have hL' : (∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l))).degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hL (by exact_mod_cast Nat.le_succ n)
  rw [← hprod, sub_right_comm]
  exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hL')

theorem Vpos_subset_image {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) :
    Vpos n ⊆ Phi mu '' Ilace mu := by
  intro y hy
  set w : Fin n → ℝ := fun i => y (Fin.castSucc i) with hwdef
  set c : ℝ := y (Fin.last n) with hcdef
  have hw : ∀ i, 0 < w i := hy
  choose la hla hroot using exists_root hmu w hw c
  have hI : la ∈ Ilace mu := by
    intro i
    exact ⟨(hla (Fin.castSucc i) i).1 le_rfl,
      (hla (Fin.succ i) i).2 (by rw [Fin.le_def]; simp)⟩
  have hinj : Function.Injective la := (ilace_strictAnti hI).injective
  refine ⟨la, hI, ?_⟩
  -- R_{w,c} = ∏ (X - λ_j)
  have hpoly : (X - C c) * ∏ i, (X - C (mu i)) - ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)) =
      ∏ j, (X - C (la j)) := by
    refine eq_of_degree_sub_lt_of_eval_index_eq (s := (univ : Finset (Fin (n + 1)))) (v := la)
      hinj.injOn ?_ ?_
    · rw [card_univ, Fintype.card_fin]; exact degree_R_sub_lt mu w c la
    · intro j _
      have hR := Rf_eq_prod_sec mu w c (la j) (Jset_ne (hla j))
      rw [hroot j, mul_zero] at hR
      have e1 : eval (la j) ((X - C c) * ∏ i, (X - C (mu i)) -
          ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l))) = Rf mu w c (la j) := by
        simp [Rf, eval_prod, eval_finsetSum]
      rw [e1, hR, eval_prod, Finset.prod_eq_zero (i := j) (mem_univ _) (by simp)]
  have hpoly2 := poly_id hmu.injective la
  have hfun : ∀ t, Rf mu w c t = Rf mu (wv mu la) (cv mu la) t := by
    intro t
    have e1 := congrArg (eval t) hpoly
    have e2 := congrArg (eval t) hpoly2
    simp only [eval_sub, eval_mul, eval_X, eval_C, eval_prod, eval_finsetSum] at e1 e2
    unfold Rf
    rw [e1, e2]
  have hwe : ∀ i, w i = wv mu la i := by
    intro i
    have := hfun (mu i)
    rw [Rf_at_mu, Rf_at_mu] at this
    have hD := Dn_ne_zero hmu.injective i
    have : (w i - wv mu la i) * Dn mu i = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  have hce : c = cv mu la := by
    obtain ⟨t0, ht0⟩ : ∃ t0, t0 ∉ Set.range mu := ((Set.finite_range mu).infinite_compl).nonempty
    have hne : ∀ i, t0 ≠ mu i := fun i he => ht0 ⟨i, he.symm⟩
    have := hfun t0
    unfold Rf at this
    simp only [← hwe] at this
    have hp : (∏ i, (t0 - mu i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hne i))
    have : (cv mu la - c) * ∏ i, (t0 - mu i) = 0 := by linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hp)).symm
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Phi, Fin.snoc_last]; exact hce.symm
  · simp only [Phi, Fin.snoc_castSucc]; exact (hwe i).symm

theorem image_Phi {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) : Phi mu '' Ilace mu = Vpos n := by
  refine Set.Subset.antisymm ?_ (Vpos_subset_image hmu)
  rintro _ ⟨la, hla, rfl⟩ i
  simp only [Phi, Fin.snoc_castSucc]
  exact wv_pos hla i

end Weyl

end

-- ===== from W2a.lean =====
section

namespace Weyl

open Finset

/-- The Jacobian as a continuous linear map. -/
noncomputable def Jlin {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Jm mu la))

theorem det_Jlin {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    (Jlin mu la).det = (Jm mu la).det := by
  rw [Jlin, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']

theorem Jlin_apply {n : ℕ} (mu : Fin n → ℝ) (la v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Jlin mu la v i = ∑ j, Jm mu la i j * v j := by
  simp [Jlin, Matrix.toLin'_apply, mulVec, dotProduct]

theorem hasFDerivAt_wv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) (i : Fin n) :
    HasFDerivAt (fun la => wv mu la i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)).comp
        (Jlin mu la)) la := by
  have hj : ∀ j ∈ (univ : Finset (Fin (n + 1))), HasFDerivAt (fun la : Fin (n + 1) → ℝ => mu i - la j)
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j)) la :=
    fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j la).const_sub (mu i)
  have hp := (HasFDerivAt.finsetProd hj).const_mul (-(Dn mu i)⁻¹)
  have hf : (fun la => wv mu la i) = fun la => -(Dn mu i)⁻¹ * ∏ j, (mu i - la j) := by
    funext la; simp only [wv, div_eq_mul_inv]; ring
  rw [hf]
  refine hp.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [Jlin_apply]
  simp [Jm, div_eq_mul_inv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem hasFDerivAt_cv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun la => cv mu la)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
        (Jlin mu la)) la := by
  have hs := (HasFDerivAt.fun_sum (u := (univ : Finset (Fin (n + 1))))
    (fun j _ => hasFDerivAt_apply (𝕜 := ℝ) j la)).sub_const (∑ i, mu i)
  refine hs.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [Jlin_apply]
  simp [Jm]

theorem hasFDerivAt_Phi {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    HasFDerivAt (Phi mu) (Jlin mu la) la := by
  rw [hasFDerivAt_pi']
  intro i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · have : (fun la => Phi mu la (Fin.last n)) = fun la => cv mu la := by
      funext la; simp [Phi]
    rw [this]; exact hasFDerivAt_cv mu la
  · have : (fun la => Phi mu la (Fin.castSucc i')) = fun la => wv mu la i' := by
      funext la; simp [Phi]
    rw [this]; exact hasFDerivAt_wv mu la i'

theorem measurableSet_Ilace {n : ℕ} (mu : Fin n → ℝ) : MeasurableSet (Ilace mu) := by
  have : Ilace mu = ⋂ i : Fin n, ({la : Fin (n + 1) → ℝ | mu i < la (Fin.castSucc i)} ∩
      {la | la (Fin.succ i) < mu i}) := by
    ext la; simp [Ilace]
  rw [this]
  refine MeasurableSet.iInter (fun i => (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))

end Weyl

end

-- ===== from W3a.lean =====
section

namespace Weyl

open Finset

/-- The strictly decreasing chamber. -/
def SA (m : ℕ) : Set (Fin m → ℝ) := {ξ | StrictAnti ξ}

theorem measurableSet_SA (m : ℕ) : MeasurableSet (SA m) := by
  have : SA m = ⋂ i : Fin m, ⋂ j : Fin m, ⋂ (_ : i < j), {ξ : Fin m → ℝ | ξ j < ξ i} := by
    ext ξ; simp [SA, StrictAnti]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

theorem null_not_inj (m : ℕ) : volume {ξ : Fin m → ℝ | ¬ Function.Injective ξ} = 0 := by
  have hsub : {ξ : Fin m → ℝ | ¬ Function.Injective ξ} ⊆ ⋃ i : Fin m, ⋃ j : Fin m, ⋃ (_ : i ≠ j),
      ((LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) :
        Submodule ℝ (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq, Function.Injective] at hξ
    push_neg at hξ
    obtain ⟨i, j, hij, hne⟩ := hξ
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, by simp [hij]⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (1 : ℝ) : Fin m → ℝ) ∈
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) := by
    rw [htop]; exact Submodule.mem_top
  simp [Pi.single_apply, Ne.symm hij] at hmem

theorem eq_sort_of_strictAnti {m : ℕ} {ξ : Fin m → ℝ} {σ : Equiv.Perm (Fin m)}
    (h : StrictAnti (ξ ∘ σ)) : σ = Tuple.sort (fun i => -ξ i) := by
  rw [Tuple.eq_sort_iff]
  refine ⟨fun i j hij => ?_, fun i j hij heq => ?_⟩
  · simp only [Function.comp]
    exact neg_le_neg (h.antitone hij)
  · exfalso
    simp only [neg_inj] at heq
    exact (ne_of_gt (h hij)) heq

theorem strictAnti_sort {m : ℕ} {ξ : Fin m → ℝ} (hξ : Function.Injective ξ) :
    StrictAnti (ξ ∘ Tuple.sort (fun i => -ξ i)) := by
  have hm := Tuple.monotone_sort (fun i => -ξ i)
  have hinj : Function.Injective ((fun i => -ξ i) ∘ Tuple.sort (fun i => -ξ i)) :=
    (neg_injective.comp hξ).comp (Tuple.sort (fun i => -ξ i)).injective
  have hsm := hm.strictMono_of_injective hinj
  intro i j hij
  have := hsm hij
  simp only [Function.comp] at this ⊢
  linarith

theorem piCongrLeft_symm_eq {m : ℕ} (σ : Equiv.Perm (Fin m)) (ξ : Fin m → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) σ.symm) ξ = ξ ∘ σ := by
  funext i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m => ℝ) σ.symm ξ (σ i)
  simpa using this

end Weyl

end

-- ===== from W4a.lean =====
section

namespace Weyl

open Finset

/-- The box `Π_i (λ_{i+1}, λ_i)` of the `μ` interlacing `λ`. -/
def box {n : ℕ} (la : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i : Fin n => Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))

theorem mem_box_iff {n : ℕ} {la : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} : mu ∈ box la ↔ la ∈ Ilace mu := by
  simp only [box, Ilace, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Set.mem_setOf_eq]
  exact forall_congr' fun i => and_comm

theorem measurableSet_box {n : ℕ} (la : Fin (n + 1) → ℝ) : MeasurableSet (box la) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

theorem vdm_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ vdm v :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- The sign `∏_{i<j} (-1)`. -/
noncomputable def sgn (m : ℕ) : ℝ := ∏ i : Fin m, ∏ _j ∈ Ioi i, (-1 : ℝ)

theorem abs_sgn (m : ℕ) : |sgn m| = 1 := by
  simp [sgn, Finset.abs_prod]

theorem sgn_mul_self (m : ℕ) : sgn m * sgn m = 1 := by
  rw [← abs_mul_self, abs_mul, abs_sgn, one_mul]

theorem det_vdm_strictAnti {m : ℕ} {v : Fin m → ℝ} (hv : StrictAnti v) :
    (vandermonde v).det = sgn m * vdm v := by
  rw [det_vandermonde, vdm, sgn, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have := hv (mem_Ioi.mp hj)
  rw [abs_of_pos (by linarith)]
  ring

theorem integral_Ioo_pow {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    ∫ t in Set.Ioo a b, t ^ k = (b ^ (k + 1) - a ^ (k + 1)) / (k + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab, integral_pow]

theorem integrableOn_Ioo_pow (a b : ℝ) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (volume.restrict (Set.Ioo a b)) :=
  ((continuous_pow k).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

/-- Integral of a Vandermonde determinant over a box = determinant of the 1D moment integrals. -/
theorem integral_det_vdm {n : ℕ} (la : Fin (n + 1) → ℝ) :
    ∫ mu in box la, (vandermonde mu).det =
      (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)), t ^ (j : ℕ)).det := by
  have hrestr : (volume : Measure (Fin n → ℝ)).restrict (box la) =
      Measure.pi (fun i : Fin n => volume.restrict (Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))) := by
    rw [box, show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      Measure.restrict_pi_pi]
  rw [hrestr]
  have h1 : (fun mu : Fin n → ℝ => (vandermonde mu).det) =
      fun mu => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, mu i ^ (σ i : ℕ) := by
    funext mu
    rw [← det_transpose, det_apply']
    simp [vandermonde_apply]
  rw [h1, integral_finsetSum _ (fun σ _ => (Integrable.fintype_prod
    (f := fun i (t : ℝ) => t ^ (σ i : ℕ)) (fun i => integrableOn_Ioo_pow _ _ _)).const_mul _)]
  rw [← det_transpose, det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => t ^ (σ i : ℕ))]
  simp

theorem prod_inv_succ (n : ℕ) : ∏ j : Fin n, (1 / ((j : ℕ) + 1 : ℝ)) = 1 / (n.factorial : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => 1 / ((j : ℝ) + 1)) n, Nat.factorial_eq_prod_range_add_one]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- The row-difference determinant equals the Vandermonde determinant up to sign. -/
theorem abs_det_diff {n : ℕ} (la : Fin (n + 1) → ℝ) :
    |(Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)).det| = vdm la := by
  rw [vdm_eq_abs_det]
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
    Fin.cases (la 0 ^ (j : ℕ)) (fun i' : Fin n => la i'.succ ^ (j : ℕ) - la i'.castSucc ^ (j : ℕ)) i
    with hB
  have hdet : (vandermonde la).det = B.det := by
    refine det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => ?_) (fun i j => ?_)
    · simp [hB, vandermonde_apply]
    · simp [hB, vandermonde_apply]
  have hB2 : B.det = (B.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ i : Fin n, B i.succ 0 = 0 := by intro i; simp [hB]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp [hB, Fin.succAbove_zero]
  have hsub : B.submatrix Fin.succ Fin.succ = -(Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)) := by
    ext i j
    simp [hB, Fin.val_succ]
  rw [hdet, hB2, hsub, det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The interlacing integral `∫_{box λ} Δ(μ) dμ = Δ(λ) / n!`. -/
theorem integral_box_vdm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : StrictAnti la) :
    ∫ mu in box la, vdm mu = vdm la / (n.factorial : ℝ) := by
  have hcong : ∫ mu in box la, vdm mu = sgn n * ∫ mu in box la, (vandermonde mu).det := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_box la) (fun mu hmu => ?_)
    rw [det_vdm_strictAnti (ilace_mu_strictAnti (mem_box_iff.mp hmu)), ← mul_assoc, sgn_mul_self,
      one_mul]
  have hnn : 0 ≤ ∫ mu in box la, vdm mu :=
    setIntegral_nonneg (measurableSet_box la) (fun mu _ => vdm_nonneg mu)
  have hN : (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)), t ^ (j : ℕ)) =
      Matrix.of fun (i : Fin n) (j : Fin n) => (1 / ((j : ℕ) + 1 : ℝ)) *
        (la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)) := by
    ext i j
    have hle : la (Fin.succ i) ≤ la (Fin.castSucc i) := (hla (Fin.castSucc_lt_succ (i := i))).le
    simp only [Matrix.of_apply]
    rw [integral_Ioo_pow hle]
    ring
  have hrow := det_mul_row (fun j : Fin n => 1 / ((j : ℕ) + 1 : ℝ)) (Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1))
  simp only [Matrix.of_apply] at hrow
  rw [← abs_of_nonneg hnn, hcong, abs_mul, abs_sgn, one_mul, integral_det_vdm, hN,
    hrow, prod_inv_succ, abs_mul, abs_det_diff,
    abs_of_pos (by positivity)]
  ring

end Weyl

end

-- ===== from W2b.lean =====
section

namespace Weyl

open Finset

/-- Change of variables `y = Φ_μ(λ)` on the interlacing region (lintegral form). -/
theorem lintegral_Vpos_eq {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu)
    (g : (Fin (n + 1) → ℝ) → ENNReal) :
    ∫⁻ y in Vpos n, g y = ∫⁻ la in Ilace mu, ENNReal.ofReal (vdm la / vdm mu) * g (Phi mu la) := by
  rw [← image_Phi hmu, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_Ilace mu)
    (fun la _ => (hasFDerivAt_Phi mu la).hasFDerivWithinAt) (phi_injOn mu)]
  refine setLIntegral_congr_fun (measurableSet_Ilace mu) (fun la hla => ?_)
  rw [det_Jlin, abs_det_Jm hmu.injective (ilace_strictAnti hla).injective]

/-- Symmetrization (lintegral form). -/
theorem lintegral_sym {m : ℕ} (g : (Fin m → ℝ) → ENNReal) (hg : Measurable g)
    (hsym : ∀ σ : Equiv.Perm (Fin m), ∀ ξ, g (ξ ∘ σ) = g ξ) :
    ∫⁻ ξ, g ξ = (m.factorial : ENNReal) * ∫⁻ ξ in SA m, g ξ := by
  classical
  set S : Equiv.Perm (Fin m) → Set (Fin m → ℝ) := fun σ => {ξ | StrictAnti (ξ ∘ σ)} with hSdef
  have hSe : ∀ σ, S σ = (MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) σ.symm) ⁻¹' SA m := by
    intro σ; ext ξ; simp [hSdef, SA, piCongrLeft_symm_eq]
  have hS : ∀ σ, MeasurableSet (S σ) := by
    intro σ; rw [hSe]; exact (MeasurableEquiv.measurable _) (measurableSet_SA m)
  have hinj : ∀ᵐ ξ ∂(volume : Measure (Fin m → ℝ)), Function.Injective ξ := by
    rw [ae_iff]; exact null_not_inj m
  have hae : (fun ξ => g ξ) =ᵐ[volume] fun ξ => ∑ σ, (S σ).indicator g ξ := by
    filter_upwards [hinj] with ξ hξ
    rw [Finset.sum_eq_single (Tuple.sort (fun i => -ξ i))]
    · rw [Set.indicator_of_mem]; exact strictAnti_sort hξ
    · intro τ _ hτ
      rw [Set.indicator_of_notMem]
      intro hmem; exact hτ (eq_sort_of_strictAnti hmem)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [lintegral_congr_ae hae, lintegral_finsetSum _ (fun σ _ => hg.indicator (hS σ))]
  have hone : ∀ σ, ∫⁻ ξ, (S σ).indicator g ξ = ∫⁻ ξ in SA m, g ξ := by
    intro σ
    rw [lintegral_indicator (hS σ)]
    have he := volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) σ.symm
    rw [hSe, ← he.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _) g (SA m)]
    refine setLIntegral_congr_fun ((MeasurableEquiv.measurable _) (measurableSet_SA m)) (fun ξ _ => ?_)
    rw [piCongrLeft_symm_eq, hsym]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem continuous_vdm {m : ℕ} : Continuous (fun v : Fin m → ℝ => vdm v) := by
  unfold vdm; fun_prop

theorem box_subset_Icc {n : ℕ} (la : Fin (n + 1) → ℝ) :
    box la ⊆ Set.Icc (fun i : Fin n => la (Fin.succ i)) (fun i => la (Fin.castSucc i)) := by
  intro mu hmu
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hmu
  exact ⟨fun i => (hmu i).1.le, fun i => (hmu i).2.le⟩

/-- The interlacing integral, lintegral form. -/
theorem lintegral_box_vdm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : StrictAnti la) :
    ∫⁻ mu in box la, ENNReal.ofReal (vdm mu) = ENNReal.ofReal (vdm la / (n.factorial : ℝ)) := by
  rw [← integral_box_vdm hla, ofReal_integral_eq_lintegral_ofReal]
  · exact (continuous_vdm.integrableOn_Icc).mono_set (box_subset_Icc la)
  · exact Filter.Eventually.of_forall (fun mu => vdm_nonneg mu)

end Weyl

end

-- ===== from Q3a.lean =====
section

/-- `stdComplexGaussian` as a pushforward of two independent `N(0,1/2)`. -/
theorem integral_cg (f : ℂ → ℂ) (hf : AEStronglyMeasurable f SpikedWishart.SoftEdge.stdComplexGaussian) :
    ∫ z, f z ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      ∫ p, f ⟨p.1, p.2⟩ ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian at hf ⊢
  exact integral_map (φ := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hf

/-- Scalar characteristic function of the standard complex Gaussian. -/
theorem cg_char (a b : ℝ) :
    ∫ z, cexp (((a * z.re + b * z.im : ℝ) : ℂ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      cexp (-(((a ^ 2 + b ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp (((a * (⟨p.1, p.2⟩ : ℂ).re + b * (⟨p.1, p.2⟩ : ℂ).im : ℝ) : ℂ) * I) =
      cexp (a * p.1 * I) * cexp (b * p.2 * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp (a * x * I)) (fun y : ℝ => cexp (b * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `E exp(i t x²)` for `x ∼ N(0,1/2)`. -/
theorem g_sq_char (t : ℝ) :
    ∫ x, cexp ((t * x ^ 2 : ℝ) * I) ∂(gaussianReal 0 (1 / 2)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, gaussianPDFReal 0 (1 / 2) x • cexp ((t * x ^ 2 : ℝ) * I) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * cexp (-(1 - t * I) * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul]
    have h2 : (2 * Real.pi * ((1 / 2 : NNReal) : ℝ)) = Real.pi := by push_cast; ring
    have h3 : (-(x - 0) ^ 2 / (2 * ((1 / 2 : NNReal) : ℝ))) = -x ^ 2 := by push_cast; ring
    have h4 : (((-x ^ 2 : ℝ)) : ℂ) + ((t * x ^ 2 : ℝ) : ℂ) * I = -(1 - t * I) * (x : ℂ) ^ 2 := by
      push_cast; ring
    rw [h2, h3, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv, mul_assoc,
      ← Complex.exp_add, h4]
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex (by simp)]

/-- `E exp(i t |z|²) = 1/(1 - i t)` for the standard complex Gaussian. -/
theorem cg_normSq_char (t : ℝ) :
    ∫ z, cexp ((t * Complex.normSq z : ℝ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      1 / (1 - t * I) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp ((t * Complex.normSq (⟨p.1, p.2⟩ : ℂ) : ℝ) * I) =
      cexp ((t * p.1 ^ 2 : ℝ) * I) * cexp ((t * p.2 ^ 2 : ℝ) * I) := by
    intro p
    rw [← Complex.exp_add, Complex.normSq_mk]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp ((t * x ^ 2 : ℝ) * I))
    (fun y : ℝ => cexp ((t * y ^ 2 : ℝ) * I)), g_sq_char]
  have hb : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 = (Real.pi : ℂ) / (1 - t * I) := by
    rw [one_div, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by norm_num)]
  calc ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) *
        (((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ))
      = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2)⁻¹ * ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 := by
        push_cast; ring
    _ = 1 / (1 - t * I) := by
        rw [hpi, hc]; field_simp

end

-- ===== from Q3b.lean =====
section

/-- Real Frobenius pairing `Re tr(Tᴴ Y)`, written entrywise. -/
noncomputable def pair {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) : ℝ :=
  ∑ a, ∑ b, (star (T a b) * Y a b).re

theorem pair_eq_trace {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) :
    pair T Y = (trace (Tᴴ * Y)).re := by
  simp only [pair, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ) :
    pair T T = ∑ a, ∑ b, ((T a b).re ^ 2 + (T a b).im ^ 2) := by
  simp only [pair]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ)
    (h : pair T T = 0) : T = 0 := by
  rw [pair_self] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp h
  ext a b
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).mp
    (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
  have hr : (T a b).re = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  have hi : (T a b).im = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  exact Complex.ext (by simp [hr]) (by simp [hi])

/-- Characteristic function of the i.i.d. complex Gaussian array. -/
theorem sample_char (M N : ℕ) (τ : Matrix (Fin M) (Fin N) ℂ) :
    ∫ X, cexp ((pair τ (Matrix.of X) : ℂ) * I) ∂SpikedWishart.SoftEdge.sampleLaw M N =
      cexp (-((pair τ τ / 4 : ℝ) : ℂ)) := by
  have h1 : ∀ X : Fin M → Fin N → ℂ, cexp ((pair τ (Matrix.of X) : ℂ) * I) =
      ∏ m, ∏ j, cexp ((((τ m j).re * (X m j).re + (τ m j).im * (X m j).im : ℝ) : ℂ) * I) := by
    intro X
    simp only [pair, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun m _ => Finset.prod_congr rfl (fun j _ => ?_))
    congr 3
    simp [Complex.mul_re]
  simp_rw [h1]
  unfold SpikedWishart.SoftEdge.sampleLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : Fin N → ℂ) =>
    ∏ j, cexp ((((τ m j).re * (x j).re + (τ m j).im * (x j).im : ℝ) : ℂ) * I))]
  have h2 : ∀ m : Fin M, ∫ x : Fin N → ℂ, ∏ j, cexp ((((τ m j).re * (x j).re +
        (τ m j).im * (x j).im : ℝ) : ℂ) * I) ∂(Measure.pi fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) =
      ∏ j, cexp (-((((τ m j).re ^ 2 + (τ m j).im ^ 2) / 4 : ℝ) : ℂ)) := by
    intro m
    rw [integral_fintype_prod_eq_prod (fun j (z : ℂ) =>
      cexp ((((τ m j).re * z.re + (τ m j).im * z.im : ℝ) : ℂ) * I))]
    exact Finset.prod_congr rfl (fun j _ => cg_char _ _)
  simp_rw [h2]
  rw [pair_self]
  simp only [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The pairing as an `ℝ`-bilinear map on arrays. -/
noncomputable def Lpair (M N : ℕ) :
    (Fin M → Fin N → ℂ) →ₗ[ℝ] (Fin M → Fin N → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => pair (Matrix.of w) (Matrix.of v))
    (fun v1 v2 w => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)
    (fun v w1 w2 => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, star_add, add_mul, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)

theorem Lpair_apply (M N : ℕ) (v w : Fin M → Fin N → ℂ) :
    Lpair M N v w = pair (Matrix.of w) (Matrix.of v) := rfl

theorem continuous_Lpair (M N : ℕ) :
    Continuous fun p : (Fin M → Fin N → ℂ) × (Fin M → Fin N → ℂ) => Lpair M N p.1 p.2 := by
  simp only [Lpair_apply, pair, Matrix.of_apply]
  fun_prop

theorem continuous_pair_of {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => pair T (Matrix.of X)) := by
  simp only [pair, Matrix.of_apply]
  fun_prop

theorem continuous_char_pair {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => cexp ((pair T (Matrix.of X) : ℂ) * I)) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_pair_of T)).mul
    continuous_const)

theorem conjTranspose_map_star {α β : Type*} (Q : Matrix α β ℂ) : (Q.map star)ᴴ = Qᵀ := by
  ext i j; simp

theorem transpose_mul_map_star {α : Type*} [Fintype α] [DecidableEq α] (Q : Matrix α α ℂ)
    (hQ : Q ∈ unitaryGroup α ℂ) : Qᵀ * Q.map star = 1 := by
  have h := mem_unitaryGroup_iff'.mp hQ
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

theorem map_star_mul_transpose {α : Type*} [Fintype α] [DecidableEq α] (P : Matrix α α ℂ)
    (hP : P ∈ unitaryGroup α ℂ) : P.map star * Pᵀ = 1 := by
  have h := mem_unitaryGroup_iff.mp hP
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

/-- Moving a two-sided unitary action across the pairing. -/
theorem pair_unitary {M N : ℕ} (W Y : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) :
    pair W ((P * Yᵀ * Q)ᵀ) = pair (Q.map star * W * P.map star) Y := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_transpose, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_map_star, conjTranspose_map_star]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

theorem pair_unitary_self {M N : ℕ} (W : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) (hP : P ∈ unitaryGroup (Fin N) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    pair (Q.map star * W * P.map star) (Q.map star * W * P.map star) = pair W W := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_map_star, conjTranspose_map_star]
  have e : Pᵀ * (Wᴴ * Qᵀ) * (Q.map star * W * P.map star) =
      Pᵀ * (Wᴴ * (Qᵀ * Q.map star) * W) * P.map star := by
    simp only [Matrix.mul_assoc]
  rw [e, transpose_mul_map_star Q hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    map_star_mul_transpose P hP, Matrix.one_mul]

/-- Unitary invariance of the i.i.d. complex Gaussian array under `H ↦ P H Q`
(`H = (of X)ᵀ`). -/
theorem sample_invariant (M N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) (Q : Matrix (Fin M) (Fin M) ℂ)
    (hP : P ∈ unitaryGroup (Fin N) ℂ) (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map
        (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have hmeas : Measurable (fun X : Fin M → Fin N → ℂ => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) := by
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have : IsProbabilityMeasure ((SpikedWishart.SoftEdge.sampleLaw M N).map
      (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := Lpair M N) ?_ (continuous_Lpair M N) ?_
  · intro v hv h0
    apply hv
    have : Lpair M N v v = 0 := by rw [h0]; rfl
    rw [Lpair_apply] at this
    have := eq_zero_of_pair_self _ this
    funext m j
    exact congrFun (congrFun this m) j
  · intro w
    simp only [BoundedContinuousFunction.char_apply, Real.probChar_apply, Lpair_apply]
    rw [integral_map hmeas.aemeasurable (continuous_char_pair _).aestronglyMeasurable]
    have h3 : ∀ X : Fin M → Fin N → ℂ,
        pair (Matrix.of w) (Matrix.of (fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) =
          pair (Q.map star * Matrix.of w * P.map star) (Matrix.of X) := by
      intro X
      rw [← pair_unitary]
      rfl
    simp_rw [h3]
    rw [sample_char, sample_char, pair_unitary_self _ _ _ hP hQ]

end

-- ===== from W5a.lean =====
section

namespace Weyl

/-- Density of the standard exponential law. -/
noncomputable def dexp (w : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator (fun w => Real.exp (-w)) w

theorem dexp_nonneg (w : ℝ) : 0 ≤ dexp w := by
  unfold dexp; by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem measurable_dexp : Measurable dexp :=
  (Real.continuous_exp.comp continuous_neg).measurable.indicator measurableSet_Ioi

/-- The standard exponential law `Exp(1)`. -/
noncomputable def exp1 : Measure ℝ := volume.withDensity (fun w => ENNReal.ofReal (dexp w))

theorem integrable_dexp : Integrable dexp := by
  unfold dexp
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  simpa using this

theorem integral_dexp : ∫ w, dexp w = 1 := by
  unfold dexp
  rw [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero]

theorem isProb_exp1 : IsProbabilityMeasure exp1 := by
  constructor
  rw [exp1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_dexp (Eventually.of_forall dexp_nonneg),
    integral_dexp, ENNReal.ofReal_one]

theorem integral_exp1 (g : ℝ → ℂ) : ∫ w, g w ∂exp1 = ∫ w in Set.Ioi 0, (Real.exp (-w) : ℂ) * g w := by
  have hm : Measurable (fun w => (dexp w).toNNReal) := measurable_dexp.real_toNNReal
  rw [exp1, show (fun w => ENNReal.ofReal (dexp w)) = (fun w => (((dexp w).toNNReal : NNReal) : ENNReal))
    from rfl, integral_withDensity_eq_integral_smul hm]
  unfold dexp
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext w
  by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.real_smul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

theorem charFun_exp1 (t : ℝ) : charFun exp1 t = 1 / (1 - t * I) := by
  rw [charFun_apply_real, integral_exp1]
  have h : ∀ w : ℝ, (Real.exp (-w) : ℂ) * cexp (t * w * I) = cexp ((t * I - 1) * w) := by
    intro w; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [h]
  have hre : (t * I - 1 : ℂ).re < 0 := by simp
  rw [integral_exp_mul_complex_Ioi hre 0]
  have hne : (t * I - 1 : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  have hne2 : (1 - t * I : ℂ) ≠ 0 := by
    intro h0; apply hne; linear_combination -h0
  field_simp
  simp

theorem isProb_cg : IsProbabilityMeasure SpikedWishart.SoftEdge.stdComplexGaussian := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian
  exact Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- `|g|²` of a standard complex Gaussian is `Exp(1)`. -/
theorem map_normSq_cg : SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq = exp1 := by
  have := isProb_cg
  have := isProb_exp1
  have : IsProbabilityMeasure (SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_exp1, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have := cg_normSq_char t
  convert this using 3
  push_cast; ring_nf

end Weyl

end

-- ===== from W5b.lean =====
section

namespace Weyl

/-- The map `(u, v) ↦ (u + conj v)/√2`. -/
noncomputable def rot (p : ℂ × ℂ) : ℂ := ((Real.sqrt 2)⁻¹ : ℝ) • (p.1 + star p.2)

/-- Lebesgue integral of a product over `ℝ^n`. -/
theorem lintegral_pi_prod {n : ℕ} (f : Fin n → ℝ → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) = ∏ i, ∫⁻ t, f i t := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul]
    rw [volume_pi, Measure.pi_univ]
    simp
  | succ n ih =>
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    rw [← he.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hpt : ∀ y : ℝ × (Fin n → ℝ),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm y i) =
          f 0 y.1 * ∏ i : Fin n, f i.succ (y.2 i) := by
      intro y
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
    simp_rw [hpt]
    rw [Measure.volume_eq_prod, lintegral_prod_mul (f := f 0)
      (g := fun x' : Fin n → ℝ => ∏ i : Fin n, f i.succ (x' i)) (hf 0).aemeasurable
      (Finset.measurable_prod (f := fun (i : Fin n) (x' : Fin n → ℝ) => f i.succ (x' i)) Finset.univ
        (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable,
      ih (fun i => f i.succ) (fun i => hf i.succ), Fin.prod_univ_succ]

/-- The product of `n` exponential laws has density `∏ dexp(w_i)`. -/
theorem pi_exp1 (n : ℕ) :
    Measure.pi (fun _ : Fin n => exp1) =
      volume.withDensity (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) := by
  have := isProb_exp1
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : (Set.pi Set.univ s).indicator (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) =
      fun w => ∏ i, (s i).indicator (fun t => ENNReal.ofReal (dexp t)) (w i) := by
    funext w
    by_cases hw : w ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hw]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hw i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hw]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hw
      obtain ⟨i, hi⟩ := hw
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  rw [hpt, lintegral_pi_prod _ (fun i => (measurable_dexp.ennreal_ofReal).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), exp1, withDensity_apply _ (hs i)]

end Weyl

end

-- ===== from W5c.lean =====
section

namespace Weyl

/-- The GUE matrix `(Z + Zᴴ)/√2`. -/
noncomputable def gueMat {m : ℕ} (Z : Fin m → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)

/-- Bordered Hermitian matrix `[[K, b], [bᴴ, c]]`. -/
noncomputable def blk {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks K (Matrix.of fun i (_ : Fin 1) => b i) (Matrix.of fun (_ : Fin 1) j => star (b j))
      (Matrix.of fun _ _ => (c : ℂ)))

theorem blk_cc {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (i j : Fin n) :
    blk K b c (Fin.castSucc i) (Fin.castSucc j) = K i j := by
  simp [blk, reindex_apply]

theorem blk_cl {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (i : Fin n) :
    blk K b c (Fin.castSucc i) (Fin.last n) = b i := by
  simp [blk, reindex_apply]

theorem blk_lc {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (j : Fin n) :
    blk K b c (Fin.last n) (Fin.castSucc j) = star (b j) := by
  simp [blk, reindex_apply]

theorem blk_ll {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) :
    blk K b c (Fin.last n) (Fin.last n) = c := by
  simp [blk, reindex_apply]

/-- Splitting off the last coordinate of an i.i.d. vector. -/
theorem mp_lastSplit {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (fun r : Fin (n + 1) → X => (r (Fin.last n), fun j : Fin n => r (Fin.castSucc j)))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  convert h using 1
  funext r
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.succAbove_last]
  try rfl

/-- Unit phase of a complex number. -/
noncomputable def ph (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem ph_mul_norm (z : ℂ) : ph z * (‖z‖ : ℂ) = z := by
  unfold ph
  split_ifs with h
  · simp [h]
  · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    field_simp

theorem ph_mul_star (z : ℂ) : ph z * star (ph z) = 1 := by
  unfold ph
  split_ifs with h
  · simp
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

end Weyl

end

-- ===== from W5d.lean =====
section

namespace Weyl

theorem mp_normSqvec (n : ℕ) :
    MeasurePreserving (fun b : Fin n → ℂ => fun i => Complex.normSq (b i))
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (Measure.pi fun _ : Fin n => exp1) := by
  have := isProb_cg
  have := isProb_exp1
  have hsf : ∀ _ : Fin n, SigmaFinite (SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq) :=
    fun _ => by rw [map_normSq_cg]; infer_instance
  refine ⟨measurable_pi_lambda _ (fun i => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun _ => Complex.continuous_normSq.measurable.aemeasurable)]
  simp only [map_normSq_cg]

end Weyl

end

-- ===== from W6a.lean =====
section

namespace Weyl

/-- Entrywise measurable structure on square complex matrices. -/
noncomputable def matMS (m : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := MeasurableSpace.pi

attribute [local instance] matMS

theorem matBorel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

attribute [local instance] matBorel

theorem of_zero_col (n : ℕ) : (Matrix.of fun (_ : Fin n) (_ : Fin 1) => (0 : ℂ)) = 0 := by ext; simp

theorem of_zero_row (n : ℕ) : (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (0 : ℂ)) = 0 := by ext; simp

/-- Unitary invariance of a standard complex Gaussian vector. -/
theorem piCG_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun b : Fin n → ℂ => P *ᵥ b)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) := by
  have := isProb_cg
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℂ))
      (SpikedWishart.SoftEdge.sampleLaw 1 n)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) :=
    measurePreserving_funUnique _ _
  have hT : MeasurePreserving
      (fun X : Fin 1 → Fin n → ℂ => fun m j => (P * (Matrix.of X)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℂ)) j m)
      (SpikedWishart.SoftEdge.sampleLaw 1 n) (SpikedWishart.SoftEdge.sampleLaw 1 n) := by
    refine ⟨?_, sample_invariant 1 n P 1 hP (one_mem _)⟩
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have hc := he.comp (hT.comp he.symm)
  convert hc using 1
  funext b
  ext j
  simp [MeasurableEquiv.funUnique, mulVec, dotProduct, mul_apply]

/-- The law of the border `(b, c)`. -/
noncomputable def nu (n : ℕ) : Measure ((Fin n → ℂ) × ℝ) :=
  (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod (gaussianReal 0 1)

/-- Averaging `F` over the random border of `K`. -/
noncomputable def hfun {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal)
    (K : Matrix (Fin n) (Fin n) ℂ) : ENNReal :=
  ∫⁻ p, F (blk K p.1 p.2) ∂(nu n)

theorem ofOne : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (((1 : ℝ)) : ℂ)) = 1 := by
  ext i j
  simp [Matrix.one_apply, Subsingleton.elim i j]

theorem blk_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    blk U 0 1 ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  unfold blk
  simp only [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
    fromBlocks_conjTranspose, fromBlocks_multiply, ofOne, Pi.zero_apply, star_zero, of_zero_col,
    of_zero_row, conjTranspose_zero, conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one, hUU, fromBlocks_one, submatrix_one_equiv]

theorem measurableSet_Vpos (n : ℕ) : MeasurableSet (Vpos n) := by
  have : Vpos n = ⋂ i : Fin n, {y : Fin (n + 1) → ℝ | 0 < y (Fin.castSucc i)} := by
    ext y; simp [Vpos]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply _)

end Weyl

end

-- ===== from W6b.lean =====
section

namespace Weyl

attribute [local instance] matMS matBorel

/-- Unitary invariance of a function of a matrix. -/
def UInv (m : ℕ) (F : Matrix (Fin m) (Fin m) ℂ → ENNReal) : Prop :=
  ∀ U ∈ unitaryGroup (Fin m) ℂ, ∀ A, F (U * A * star U) = F A

theorem vdm_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (ξ : Fin m → ℝ) : vdm (ξ ∘ σ) = vdm ξ := by
  rw [vdm_eq_abs_det, vdm_eq_abs_det]
  have : vandermonde (ξ ∘ σ) = (vandermonde ξ).submatrix σ id := by
    ext i j; simp [vandermonde_apply]
  rw [this, det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem measurableSet_E (n : ℕ) :
    MeasurableSet {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} := by
  have : {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} =
      ⋂ i : Fin n, ({p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.1 i < p.2 (Fin.castSucc i)} ∩
        {p | p.2 (Fin.succ i) < p.1 i}) := by
    ext p; simp [Ilace]
  rw [this]
  refine MeasurableSet.iInter fun i => (measurableSet_lt ?_ ?_).inter (measurableSet_lt ?_ ?_)
  all_goals fun_prop

end Weyl

end

end SpikedWishart.Separated.Lib

-- ===== from S0.lean =====


open MeasureTheory Set Matrix
open scoped ComplexOrder Pointwise

namespace SWL302Eig

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem isHermitian_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    ((x : ℂ) • (1 : Matrix n n ℂ) - A).IsHermitian := by
  refine IsHermitian.sub ?_ hA
  simp [IsHermitian, conjTranspose_smul]

/-- The eigenvalues of `x - A` are the `x - λ_j(A)`, as a statement about any property. -/
theorem forall_eig_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) (P : ℝ → Prop) :
    (∀ i, P ((isHermitian_smul_one_sub hA x).eigenvalues i)) ↔ ∀ j, P (x - hA.eigenvalues j) := by
  set hH := isHermitian_smul_one_sub hA x
  have hs : spectrum ℂ ((x : ℂ) • (1 : Matrix n n ℂ) - A) = ({(x : ℂ)} : Set ℂ) - spectrum ℂ A := by
    rw [← Algebra.algebraMap_eq_smul_one, spectrum.singleton_sub_eq]
  rw [hH.spectrum_eq_image_range, hA.spectrum_eq_image_range] at hs
  constructor
  · intro h j
    have hmem : ((x - hA.eigenvalues j : ℝ) : ℂ) ∈ (RCLike.ofReal '' Set.range hH.eigenvalues : Set ℂ) := by
      rw [hs]
      exact Set.mem_sub.mpr ⟨x, rfl, _, ⟨_, ⟨j, rfl⟩, rfl⟩, by push_cast; rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem
    have : hH.eigenvalues i = x - hA.eigenvalues j := RCLike.ofReal_injective hi
    rw [← this]; exact h i
  · intro h i
    have hmem : ((hH.eigenvalues i : ℝ) : ℂ) ∈ ({(x : ℂ)} - RCLike.ofReal '' Set.range hA.eigenvalues : Set ℂ) := by
      rw [← hs]; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨y, hy, z, ⟨_, ⟨j, rfl⟩, rfl⟩, hyz⟩ := Set.mem_sub.mp hmem
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have : hH.eigenvalues i = x - hA.eigenvalues j := by
      have h2 : ((x - hA.eigenvalues j : ℝ) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) := by
        rw [← hyz]; push_cast; rfl
      exact_mod_cast h2.symm
    rw [this]; exact h j

theorem eig_le_iff_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (∀ j, hA.eigenvalues j ≤ x) ↔ ((x : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef := by
  rw [(isHermitian_smul_one_sub hA x).posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  simp only [Pi.zero_apply]
  rw [forall_eig_smul_one_sub hA x (fun t => 0 ≤ t)]
  simp only [sub_nonneg]
end SWL302Eig

namespace SWL302

open SpikedWishart.FixedDim

noncomputable def matMS (m : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := MeasurableSpace.pi

attribute [local instance] matMS

theorem matBorel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

attribute [local instance] matBorel

/-- Child statement A (James 1964; Forrester, Log-gases, Prop. 3.2.2): Weyl integration formula for the
null complex Wishart matrix `W = Σ_m g_m g_mᴴ`, `M ≥ k`, in lintegral form. -/
def LagWeyl (k M : ℕ) : Prop :=
  ∃ c : ENNReal, ∀ F : (Fin k → Fin k → ℂ) → ENNReal, Measurable F →
    (∀ U ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ A : Matrix (Fin k) (Fin k) ℂ, F (U * A * star U) = F A) →
    ∫⁻ G, F (fun i j => ∑ m, G m i * star (G m j)) ∂(sampleLaw M k) =
      c * ∫⁻ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)),
        F (Matrix.diagonal fun i => (x i : ℂ)) *
          ENNReal.ofReal (vandSq x * ∏ j, Real.exp (-x j) * x j ^ (M - k))

lemma vandSq_affine {k : ℕ} (c b : ℝ) (ξ : Fin k → ℝ) :
    vandSq (fun j => c + b * ξ j) =
      (∏ i : Fin k, ∏ j : Fin k, if i < j then b ^ 2 else 1) * vandSq ξ := by
  unfold vandSq
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> ring

lemma cov {k : ℕ} (c : Fin k → ℝ) (b : ℝ) (hb : 0 < b) (F : (Fin k → ℝ) → ℝ) :
    ∫ y, F y = b ^ k * ∫ ξ, F (c + b • ξ) := by
  have h1 : ∫ ξ, F (c + b • ξ) = |(b ^ k)⁻¹| • ∫ z, F (c + z) := by
    have := Measure.integral_comp_smul (volume : Measure (Fin k → ℝ)) (fun z => F (c + z)) b
    rw [Module.finrank_fin_fun] at this
    exact this
  have h2 : ∫ z, F (c + z) = ∫ y, F y := integral_add_left_eq_self (μ := (volume : Measure (Fin k → ℝ))) (f := F) c
  have hbk : 0 < b ^ k := pow_pos hb k
  rw [h1, h2, smul_eq_mul, abs_of_pos (inv_pos.mpr hbk), ← mul_assoc, mul_inv_cancel₀ hbk.ne',
    one_mul]


theorem isClosed_psdSet {k : ℕ} (x : ℝ) :
    IsClosed {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} := by
  have : OrderClosedTopology ℂ := Complex.orderClosedTopology
  have hset : {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} =
      {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A)ᴴ =
        (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A} ∩
      ⋂ v : Fin k → ℂ, {A : Matrix (Fin k) (Fin k) ℂ |
        0 ≤ star v ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) *ᵥ v)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [hset]
  have hc : Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) :=
    continuous_const.sub continuous_id
  refine (isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun v => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (hc.matrix_mulVec continuous_const)

theorem psd_conj {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    {A : Matrix (Fin k) (Fin k) ℂ} (h : ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U).PosSemidef := by
  have hUU : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have e1 : U * ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) * star U =
      (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
  rw [← e1, star_eq_conjTranspose]
  exact h.mul_mul_conjTranspose_same U

theorem psd_conj_iff {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U).PosSemidef ↔
      ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef := by
  refine ⟨fun h => ?_, psd_conj x hU⟩
  have hU' : star U ∈ unitaryGroup (Fin k) ℂ := Unitary.star_mem hU
  have h2 := psd_conj x hU' h
  have hUU' : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have e : star U * (U * A * star U) * star (star U) = A := by
    rw [star_star, Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one, ← Matrix.mul_assoc, hUU',
      Matrix.one_mul]
  rwa [e] at h2

theorem diag_psd_iff {k : ℕ} (x : ℝ) (ξ : Fin k → ℝ) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - diagonal fun i => (ξ i : ℂ)).PosSemidef ↔
      ξ ∈ Set.pi Set.univ (fun _ : Fin k => Set.Iic x) := by
  have e : (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - (diagonal fun i => (ξ i : ℂ)) =
      diagonal fun i => ((x - ξ i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, one_apply]
  rw [e, posSemidef_diagonal_iff]
  simp only [Complex.zero_le_real, sub_nonneg, Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]

/-- The unnormalised Wishart matrix `W = Σ_m g_m g_mᴴ`. -/
noncomputable def Wm {M k : ℕ} (G : Fin M → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ m, G m i * star (G m j)

theorem continuous_Wm (M k : ℕ) : Continuous (fun G : Fin M → Fin k → ℂ => Wm G) := by
  unfold Wm
  fun_prop

theorem sampleCov_eq (M k : ℕ) (π₁ : ℝ) (hπ₁ : 0 < π₁) (G : Fin M → Fin k → ℂ) :
    SpikedWishart.Separated.sampleCov M 1 (fun _ => π₁⁻¹) G = (((M : ℝ) * π₁ : ℝ) : ℂ)⁻¹ • Wm G := by
  have hsq : ((Real.sqrt π₁⁻¹ : ℝ) : ℂ) * ((Real.sqrt π₁⁻¹ : ℝ) : ℂ) = ((π₁⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.mpr hπ₁.le)]
  ext i j
  unfold SpikedWishart.Separated.sampleCov SpikedWishart.Separated.sampleVec Wm
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change (M : ℂ)⁻¹ * _ = (((M : ℝ) * π₁ : ℝ) : ℂ)⁻¹ * ∑ m, G m i * star (G m j)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.one_mulVec, Pi.star_apply, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  have e : (((M : ℝ) * π₁ : ℝ) : ℂ)⁻¹ = (M : ℂ)⁻¹ * ((π₁⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, ← hsq]
  ring

theorem event_eq (M k : ℕ) (hk : 1 ≤ k) (π₁ : ℝ) (hπ₁ : 0 < π₁) (hM : 0 < M) (t : ℝ) :
    {Y : Fin M → Fin k → ℂ | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
      (fun Y => Wm Y) ⁻¹'
        {A : Matrix (Fin k) (Fin k) ℂ |
          (((M * π₁ * t : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hβ : (0 : ℝ) < M * π₁ := mul_pos (Nat.cast_pos.mpr hM) hπ₁
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  unfold SpikedWishart.Separated.largestEig
  rw [ciSup_le_iff (Set.finite_range _).bddAbove, SWL302Eig.eig_le_iff_posSemidef, sampleCov_eq M k π₁ hπ₁]
  set β : ℝ := M * π₁ with hβdef
  have key : ((β * t : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - Wm Y =
      (β : ℂ) • ((t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - ((β : ℂ))⁻¹ • Wm Y) := by
    have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hb, one_smul]
    push_cast
    rfl
  rw [key]
  constructor
  · intro h
    exact h.smul (Complex.zero_le_real.mpr hβ.le)
  · intro h
    have h2 := h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hβ.le))
    have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    rwa [smul_smul, ← Complex.ofReal_inv, Complex.ofReal_inv, inv_mul_cancel₀ hb, one_smul] at h2

/-- Laguerre weight in the unscaled variable. -/
noncomputable def lag {k : ℕ} (a : ℕ) (x : Fin k → ℝ) : ℝ :=
  vandSq x * ∏ j, Real.exp (-x j) * x j ^ a

theorem lag_smul (k M : ℕ) (π₁ : ℝ) (y : Fin k → ℝ) :
    lag (M - k) (((M : ℝ) * π₁) • y) =
      ((∏ i : Fin k, ∏ j : Fin k, if i < j then ((M : ℝ) * π₁) ^ 2 else 1) *
        ((M : ℝ) * π₁) ^ ((M - k) * k)) * w M π₁ y := by
  unfold lag w
  have hy : (((M : ℝ) * π₁) • y) = fun j => 0 + ((M : ℝ) * π₁) * y j := by
    funext j; simp
  rw [hy, vandSq_affine]
  have hpt : ∀ j, Real.exp (-(0 + (M : ℝ) * π₁ * y j)) * (0 + (M : ℝ) * π₁ * y j) ^ (M - k) =
      ((M : ℝ) * π₁) ^ (M - k) * (Real.exp (-(M : ℝ) * π₁ * y j) * y j ^ (M - k)) := by
    intro j
    rw [zero_add, mul_pow]
    have : -((M : ℝ) * π₁ * y j) = -(M : ℝ) * π₁ * y j := by ring
    rw [this]; ring
  rw [Finset.prod_congr rfl fun j _ => hpt j, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  ring

theorem scale_int (k M : ℕ) (π₁ : ℝ) (hβ : 0 < (M : ℝ) * π₁) (A B : Set (Fin k → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : ∀ y, ((M : ℝ) * π₁) • y ∈ A ↔ y ∈ B) :
    ∫ x in A, lag (M - k) x =
      ((M : ℝ) * π₁) ^ k * ((∏ i : Fin k, ∏ j : Fin k, if i < j then ((M : ℝ) * π₁) ^ 2 else 1) *
        ((M : ℝ) * π₁) ^ ((M - k) * k)) * ∫ y in B, w M π₁ y := by
  rw [← integral_indicator hA, cov (0 : Fin k → ℝ) _ hβ (A.indicator (lag (M - k)))]
  have h : ∫ y, A.indicator (lag (M - k)) ((0 : Fin k → ℝ) + ((M : ℝ) * π₁) • y) =
      ((∏ i : Fin k, ∏ j : Fin k, if i < j then ((M : ℝ) * π₁) ^ 2 else 1) *
        ((M : ℝ) * π₁) ^ ((M - k) * k)) * ∫ y in B, w M π₁ y := by
    rw [← integral_indicator hB, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [zero_add]
    by_cases h : y ∈ B
    · rw [Set.indicator_of_mem ((hAB y).mpr h), Set.indicator_of_mem h, lag_smul]
    · rw [Set.indicator_of_notMem (fun h' => h ((hAB y).mp h')), Set.indicator_of_notMem h, mul_zero]
  rw [h]
  ring

theorem ind_psd_conj {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) (U * A * star U) =
      {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) A := by
  by_cases h : ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef
  · rw [Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) ((psd_conj_iff x hU A).mpr h),
      Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) h]
    rfl
  · rw [Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) (fun h' => h ((psd_conj_iff x hU A).mp h')),
      Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) h]

theorem ind_diag {k : ℕ} (x : ℝ) (ξ : Fin k → ℝ) :
    {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) (diagonal fun i => (ξ i : ℂ)) =
      (Set.pi Set.univ (fun _ : Fin k => Set.Iic x)).indicator 1 ξ := by
  by_cases h : ξ ∈ Set.pi Set.univ (fun _ : Fin k => Set.Iic x)
  · rw [Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) ((diag_psd_iff x ξ).mpr h), Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) (fun h' => h ((diag_psd_iff x ξ).mp h')),
      Set.indicator_of_notMem h]

theorem lag_continuous (k a : ℕ) : Continuous (lag (k := k) a) := by
  unfold lag vandSq
  refine Continuous.mul (continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_) ?_
  · split_ifs <;> fun_prop
  · fun_prop

theorem lag_nonneg {k : ℕ} (a : ℕ) (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) : 0 ≤ lag a x := by
  unfold lag vandSq
  refine mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_)
    (Finset.prod_nonneg fun j _ => ?_)
  · split_ifs <;> positivity
  · exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (hx j) _)

lemma cancel_aux (K a b : ℝ) (hK : K ≠ 0) : (K * a)⁻¹ * (K * b) = a⁻¹ * b := by
  rw [mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hK, one_mul]

/-- Step B: the eigenvalue CDF (302) from the Weyl formula `LagWeyl k M`. -/
theorem eq302_of_lag (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (t : ℝ)
    (H : LagWeyl k M) :
    (sampleLaw M k).real {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
      (C M k π₁)⁻¹ * ∫ y in Set.pi univ (fun _ : Fin k => Ioc 0 t), w M π₁ y := by
  obtain ⟨c, hc⟩ := H
  have hM : 0 < M := by omega
  have hβ : (0 : ℝ) < (M : ℝ) * π₁ := mul_pos (Nat.cast_pos.mpr hM) hπ₁
  have hOm : MeasurableSet (Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hPm : MeasurableSet (Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) ((M : ℝ) * π₁ * t))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hQm : MeasurableSet (Set.pi univ (fun _ : Fin k => Iic ((M : ℝ) * π₁ * t))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Iic
  -- normalisation
  have e1 : c * ∫⁻ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), ENNReal.ofReal (lag (M - k) x) = 1 := by
    have h := hc (fun _ => 1) measurable_const (fun _ _ _ => rfl)
    simp only [lintegral_const, measure_univ, mul_one, one_mul] at h
    exact h.symm
  -- the CDF event
  have hS := isClosed_psdSet (k := k) ((M : ℝ) * π₁ * t)
  have hE : MeasurableSet ((fun Y => Wm Y) ⁻¹'
      {A : Matrix (Fin k) (Fin k) ℂ |
        (((M * π₁ * t : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) :=
    (hS.preimage (continuous_Wm M k)).measurableSet
  have e2 : sampleLaw M k {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
      c * ∫⁻ x in Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) ((M : ℝ) * π₁ * t)),
        ENNReal.ofReal (lag (M - k) x) := by
    have h2 := hc ({A : Matrix (Fin k) (Fin k) ℂ |
        (((M * π₁ * t : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator 1)
      (by exact measurable_const.indicator hS.measurableSet)
      (fun U hU A => ind_psd_conj _ hU A)
    rw [event_eq M k hk π₁ hπ₁ hM t, ← lintegral_indicator_one hE]
    refine h2.trans ?_
    congr 1
    have hPQ : Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) ((M : ℝ) * π₁ * t)) =
        Set.pi univ (fun _ : Fin k => Iic ((M : ℝ) * π₁ * t)) ∩ Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Set.mem_Ioi,
        Set.mem_Ioc]
      exact ⟨fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩, fun h i => ⟨h.2 i, h.1 i⟩⟩
    rw [hPQ, ← Measure.restrict_restrict hQm, ← lintegral_indicator hQm]
    refine lintegral_congr fun x => ?_
    rw [ind_diag]
    by_cases hx : x ∈ Set.pi univ (fun _ : Fin k => Iic ((M : ℝ) * π₁ * t))
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  -- to reals
  have hmeas : ∀ (S : Set (Fin k → ℝ)), AEStronglyMeasurable (lag (M - k)) (volume.restrict S) :=
    fun S => (lag_continuous k (M - k)).aestronglyMeasurable
  have iO : (∫⁻ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), ENNReal.ofReal (lag (M - k) x)).toReal =
      ∫ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), lag (M - k) x := by
    refine (integral_eq_lintegral_of_nonneg_ae ?_ (hmeas _)).symm
    exact (ae_restrict_iff' hOm).mpr (Filter.Eventually.of_forall fun x hx =>
      lag_nonneg _ x fun j => le_of_lt (hx j (Set.mem_univ j)))
  have iP : (∫⁻ x in Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) ((M : ℝ) * π₁ * t)),
      ENNReal.ofReal (lag (M - k) x)).toReal =
      ∫ x in Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) ((M : ℝ) * π₁ * t)), lag (M - k) x := by
    refine (integral_eq_lintegral_of_nonneg_ae ?_ (hmeas _)).symm
    exact (ae_restrict_iff' hPm).mpr (Filter.Eventually.of_forall fun x hx =>
      lag_nonneg _ x fun j => le_of_lt (hx j (Set.mem_univ j)).1)
  have r1 := congrArg ENNReal.toReal e1
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at r1
  have hcR := eq_inv_of_mul_eq_one_left r1
  have sO := scale_int k M π₁ hβ _ _ hOm hOm (fun y => by
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioi, Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun j => ⟨fun h => (pos_iff_pos_of_mul_pos h).mp hβ, fun h => mul_pos hβ h⟩)
  have sP := scale_int k M π₁ hβ _ (Set.pi univ (fun _ : Fin k => Ioc (0 : ℝ) t)) hPm
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) (fun y => by
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun j => and_congr ⟨fun h => (pos_iff_pos_of_mul_pos h).mp hβ, fun h => mul_pos hβ h⟩ ?_
    exact mul_le_mul_iff_of_pos_left hβ)
  have hK : (M : ℝ) * π₁ ^ k * 0 = 0 := by ring
  rw [measureReal_def, e2, ENNReal.toReal_mul, hcR, iO, iP, sO, sP]
  unfold C
  refine cancel_aux _ _ _ (ne_of_gt (mul_pos (pow_pos hβ k) (mul_pos
    (Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_) (pow_pos hβ _))))
  split_ifs <;> positivity

/-! ## Array form of the Weyl formula (A2) and its consequence `LagWeyl` -/

/-- The `M × k` matrix with `√x_j` at `(j, j)` and zeros elsewhere. -/
noncomputable def Emb (M k : ℕ) (x : Fin k → ℝ) : Matrix (Fin M) (Fin k) ℂ :=
  fun m j => if (m : ℕ) = j then ((Real.sqrt (x j) : ℝ) : ℂ) else 0

/-- Weyl formula for the Gaussian array, for bi-unitarily invariant functions. -/
def LagWeyl2 (k M : ℕ) : Prop :=
  ∃ c : ENNReal, ∀ F : (Fin M → Fin k → ℂ) → ENNReal, Measurable F →
    (∀ Q ∈ Matrix.unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G) →
    (∀ V ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G) →
    ∫⁻ G, F G ∂(sampleLaw M k) =
      c * ∫⁻ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), F (Emb M k x) * ENNReal.ofReal (lag (M - k) x)

theorem Wm_eq {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) : Wm G = (Gᴴ * G)ᵀ := by
  ext i j
  simp only [Wm, transpose_apply, Matrix.mul_apply, conjTranspose_apply]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem Wm_mul_left {M k : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : Wm (Q * G) = Wm G := by
  have h : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  rw [star_eq_conjTranspose] at h
  rw [Wm_eq, Wm_eq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h, Matrix.one_mul]

theorem ct_transpose {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : Aᵀᴴ = Aᴴᵀ := by
  ext i j; rfl

theorem transpose_mem_unitary {k : ℕ} {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ) :
    Vᵀ ∈ unitaryGroup (Fin k) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  rw [star_eq_conjTranspose, ct_transpose, ← transpose_mul, ← star_eq_conjTranspose, h, transpose_one]

theorem Wm_mul_right {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) (V : Matrix (Fin k) (Fin k) ℂ) :
    Wm (G * V) = Vᵀ * Wm G * star (Vᵀ) := by
  rw [Wm_eq, Wm_eq, conjTranspose_mul, star_eq_conjTranspose, ct_transpose,
    show Vᴴ * Gᴴ * (G * V) = Vᴴ * (Gᴴ * G) * V by simp only [Matrix.mul_assoc],
    transpose_mul, transpose_mul, Matrix.mul_assoc]

theorem Wm_Emb {M k : ℕ} (hk : k ≤ M) (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) :
    Wm (Emb M k x) = diagonal fun i => (x i : ℂ) := by
  ext i j
  unfold Wm Emb
  rw [Finset.sum_eq_single (Fin.castLE hk i)]
  · by_cases hij : i = j
    · subst hij
      simp only [Fin.coe_castLE, if_true, diagonal_apply_eq, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hx i)]
    · have : ¬ ((Fin.castLE hk i : ℕ) = j) := fun h => hij (Fin.ext (by simpa using h))
      simp [this, hij]
      exact Or.inr fun h => absurd (Fin.ext h) hij
  · intro m _ hm
    have : ¬ ((m : ℕ) = i) := fun h => hm (Fin.ext (by simpa using h))
    simp [this]
  · simp

theorem lagWeyl_of_two (k M : ℕ) (hk : k ≤ M) (H : LagWeyl2 k M) : LagWeyl k M := by
  obtain ⟨c, hc⟩ := H
  refine ⟨c, fun F hFm hFinv => ?_⟩
  have h := hc (fun G => F (Wm G)) (hFm.comp (continuous_Wm M k).measurable)
    (fun Q hQ G => congrArg F (Wm_mul_left hQ G))
    (fun V hV G => (congrArg F (Wm_mul_right G V)).trans (hFinv _ (transpose_mem_unitary hV) _))
  refine h.trans ?_
  congr 1
  refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) fun x hx => ?_
  rw [Wm_Emb hk x fun j => le_of_lt (hx j (Set.mem_univ j))]
  rfl

/-- Polar step: a matrix with diagonal Gram matrix is a unitary times `Emb`. -/
theorem exists_unitary_of_gram {M k : ℕ} (hk : k ≤ M) (N : Matrix (Fin M) (Fin k) ℂ) (x : Fin k → ℝ)
    (hx : ∀ j, 0 < x j) (hN : Nᴴ * N = diagonal fun j => (x j : ℂ)) :
    ∃ Q ∈ unitaryGroup (Fin M) ℂ, N = Q * Emb M k x := by
  classical
  have hs0 : ∀ j, ((Real.sqrt (x j) : ℝ) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (Real.sqrt_pos.mpr (hx j)).ne'
  have hgram : ∀ i j, ∑ m, star (N m i) * N m j = if i = j then (x i : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun hN i) j
    rw [Matrix.mul_apply, diagonal_apply] at this
    simpa [conjTranspose_apply] using this
  let u : Fin k → EuclideanSpace ℂ (Fin M) :=
    fun j => WithLp.toLp 2 (fun m => N m j / ((Real.sqrt (x j) : ℝ) : ℂ))
  have hon : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [PiLp.inner_apply]
    have e : ∀ m, inner ℂ (u i m) (u j m) =
        star (N m i) * N m j / (((Real.sqrt (x i) : ℝ) : ℂ) * ((Real.sqrt (x j) : ℝ) : ℂ)) := by
      intro m
      simp only [u, PiLp.toLp_apply, RCLike.inner_apply, map_div₀, Complex.conj_ofReal]
      rw [Complex.star_def]
      field_simp
    rw [Finset.sum_congr rfl fun m _ => e m, ← Finset.sum_div, hgram]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hx i).le]
      exact div_self (by exact_mod_cast (hx i).ne')
    · exact zero_div _
  let v : Fin M → EuclideanSpace ℂ (Fin M) := fun m => if h : (m : ℕ) < k then u ⟨m, h⟩ else 0
  let s : Set (Fin M) := {m | (m : ℕ) < k}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    have e : s.domRestrict v = u ∘ (fun m : s => (⟨m.1, m.2⟩ : Fin k)) := by
      funext m
      simp only [Set.domRestrict, Function.comp_apply, v]
      exact dif_pos (show ((m : Fin M) : ℕ) < k from m.2)
    rw [e]
    refine hon.comp _ fun a b h => ?_
    exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun a m => b m a, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext m m'
    rw [Matrix.mul_apply, one_apply]
    simp only [Matrix.star_apply, Matrix.of_apply]
    have h := orthonormal_iff_ite.mp b.orthonormal m m'
    rw [PiLp.inner_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [RCLike.inner_apply]
    ring
  · ext m j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hk j)]
    simp only [Matrix.of_apply]
    · have hmem : Fin.castLE hk j ∈ s := by simp [s]
      rw [hb _ hmem]
      simp only [v, Fin.coe_castLE, dif_pos j.2, Emb, if_true, u, PiLp.toLp_apply]
      rw [div_mul_cancel₀ _ (hs0 j)]
    · intro a _ ha
      have : ¬ ((a : ℕ) = j) := fun h => ha (Fin.ext (by simpa using h))
      simp [Emb, this]
    · simp

end SWL302

-- ===== from S1.lean =====

/-! S1: column split of the Gaussian array and the border average `hW` with its invariances.
Needs (prefix) 53ec8574_w6b.lean and the main draft d80e94b4.lean. -/

namespace SWL302

open MeasureTheory Matrix SpikedWishart.FixedDim

/-- The standard complex Gaussian vector on `ℂ^M`. -/
noncomputable def cgv (M : ℕ) : Measure (Fin M → ℂ) := Measure.pi fun _ => stdComplexGaussian

theorem cgv.isProb (M : ℕ) : IsProbabilityMeasure (cgv M) := by
  unfold cgv; infer_instance

attribute [local instance] cgv.isProb

/-- Append the column `g` to the array `G'`. -/
def join {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) : Fin M → Fin (n + 1) → ℂ :=
  fun m => Fin.snoc (G' m) (g m)

theorem join_castSucc {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) (m : Fin M) (j : Fin n) :
    join G' g m (Fin.castSucc j) = G' m j := by
  simp [join]

theorem join_last {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) (m : Fin M) :
    join G' g m (Fin.last n) = g m := by
  simp [join]

theorem continuous_join (M n : ℕ) :
    Continuous (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => join p.1 p.2) := by
  refine continuous_pi fun m => continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last => simp only [join_last]; fun_prop
  | cast j => simp only [join_castSucc]; fun_prop

theorem mp_colSplit (M n : ℕ) :
    MeasurePreserving
      (fun G : Fin M → Fin (n + 1) → ℂ => ((fun m j => G m (Fin.castSucc j)), fun m => G m (Fin.last n)))
      (sampleLaw M (n + 1)) ((sampleLaw M n).prod (cgv M)) := by
  have hrow : MeasurePreserving
      (fun r : Fin (n + 1) → ℂ => ((fun j => r (Fin.castSucc j)), r (Fin.last n)))
      (Measure.pi fun _ => stdComplexGaussian)
      ((Measure.pi fun _ : Fin n => stdComplexGaussian).prod stdComplexGaussian) :=
    Measure.measurePreserving_swap.comp
      (SpikedWishart.Separated.Lib.Weyl.mp_lastSplit stdComplexGaussian n)
  have hpi := measurePreserving_pi (fun _ : Fin M => Measure.pi fun _ : Fin (n + 1) => stdComplexGaussian)
    (fun _ => (Measure.pi fun _ : Fin n => stdComplexGaussian).prod stdComplexGaussian) (fun _ => hrow)
  have h3 := measurePreserving_arrowProdEquivProdArrow (Fin n → ℂ) ℂ (Fin M)
    (fun _ => Measure.pi fun _ : Fin n => stdComplexGaussian) (fun _ => stdComplexGaussian)
  exact h3.comp hpi

/-- Border average: integrate out the last column. -/
noncomputable def hW {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (G' : Fin M → Fin n → ℂ) : ENNReal :=
  ∫⁻ g, F (join G' g) ∂(cgv M)

theorem measurable_hW {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F) :
    Measurable (hW F) :=
  (hFm.comp (continuous_join M n).measurable).lintegral_prod_right'

theorem step_eq2 {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F) :
    ∫⁻ G, F G ∂(sampleLaw M (n + 1)) = ∫⁻ G', hW F G' ∂(sampleLaw M n) := by
  have hj : ∀ G : Fin M → Fin (n + 1) → ℂ,
      join (fun m j => G m (Fin.castSucc j)) (fun m => G m (Fin.last n)) = G := by
    intro G; funext m; exact Fin.snoc_init_self (G m)
  have hm : Measurable (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => F (join p.1 p.2)) :=
    hFm.comp (continuous_join M n).measurable
  calc ∫⁻ G, F G ∂(sampleLaw M (n + 1))
      = ∫⁻ G, (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => F (join p.1 p.2))
          ((fun m j => G m (Fin.castSucc j)), fun m => G m (Fin.last n)) ∂(sampleLaw M (n + 1)) := by
        simp only [hj]
    _ = ∫⁻ p, F (join p.1 p.2) ∂((sampleLaw M n).prod (cgv M)) := (mp_colSplit M n).lintegral_comp hm
    _ = _ := lintegral_prod _ hm.aemeasurable

theorem join_mul_left {M n : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G' : Matrix (Fin M) (Fin n) ℂ) (g : Fin M → ℂ) :
    join (Q * G') g = Q * Matrix.of (join G' (star Q *ᵥ g)) := by
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  funext m j
  induction j using Fin.lastCases with
  | last =>
    simp only [join, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply]
    change g m = (Q *ᵥ (star Q *ᵥ g)) m
    rw [mulVec_mulVec, hQQ, one_mulVec]
  | cast j =>
    simp only [join, Fin.snoc_castSucc, Matrix.mul_apply, Matrix.of_apply]

theorem hW_left {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F)
    (hF : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ) (G' : Matrix (Fin M) (Fin n) ℂ) :
    hW F (Q * G') = hW F G' := by
  have hmp : MeasurePreserving (fun g : Fin M → ℂ => star Q *ᵥ g) (cgv M) (cgv M) := by
    have := SpikedWishart.Separated.Lib.Weyl.piCG_unitary (star Q) (Unitary.star_mem hQ)
    exact this
  have hf : Measurable (fun g : Fin M → ℂ => F (join G' g)) :=
    hFm.comp ((continuous_join M n).comp (continuous_const.prodMk continuous_id)).measurable
  unfold hW
  rw [← hmp.lintegral_comp hf]
  refine lintegral_congr fun g => ?_
  rw [join_mul_left hQ G' g, hF Q hQ]
  rfl

theorem join_mul_right {M n : ℕ} (G' : Matrix (Fin M) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (g : Fin M → ℂ) :
    join (G' * V) g =
      Matrix.of (join G' g) * SpikedWishart.Separated.Lib.Weyl.blk V 0 1 := by
  funext m j
  induction j using Fin.lastCases with
  | last =>
    simp only [join, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, SpikedWishart.Separated.Lib.Weyl.blk_cl, SpikedWishart.Separated.Lib.Weyl.blk_ll]
    simp
  | cast j =>
    simp only [join, Fin.snoc_castSucc, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      SpikedWishart.Separated.Lib.Weyl.blk_cc, SpikedWishart.Separated.Lib.Weyl.blk_lc]
    simp

theorem hW_right {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hF : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ) (G' : Matrix (Fin M) (Fin n) ℂ) :
    hW F (G' * V) = hW F G' := by
  unfold hW
  refine lintegral_congr fun g => ?_
  rw [join_mul_right, hF _ (SpikedWishart.Separated.Lib.Weyl.blk_unitary hV)]
  rfl

end SWL302

-- ===== from S2.lean =====

/-! S2: Gram reduction. A bi-unitarily invariant `F` depends only on the unitary class of the Gram
matrix (when it is positive definite); the Gram matrix of `join (Emb μ) g` is a phase conjugate of
the arrow matrix `arrowC μ (√μ ‖g‖) (Σ ‖g‖²)`. Needs prefix 53ec8574_w6b.lean, d80e94b4.lean, S1. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

theorem gram_Emb {M k : ℕ} (hk : k ≤ M) (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (Emb M k x)ᴴ * Emb M k x = diagonal fun j => (x j : ℂ) := by
  have h := Wm_Emb hk x hx
  rw [Wm_eq] at h
  rw [← transpose_transpose ((Emb M k x)ᴴ * Emb M k x), h, diagonal_transpose]

/-- A bi-invariant `F` at a matrix with Gram matrix `W diag x Wᴴ`, `x > 0`. -/
theorem F_emb {M k : ℕ} (hk : k ≤ M) (F : (Fin M → Fin k → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G)
    (B : Matrix (Fin M) (Fin k) ℂ) {W : Matrix (Fin k) (Fin k) ℂ} (hW : W ∈ unitaryGroup (Fin k) ℂ)
    (x : Fin k → ℝ) (hx : ∀ j, 0 < x j) (h : Bᴴ * B = W * diagonal (fun j => (x j : ℂ)) * star W) :
    F B = F (Emb M k x) := by
  have h1 : star W * W = 1 := mem_unitaryGroup_iff'.mp hW
  have hg : (B * W)ᴴ * (B * W) = diagonal fun j => (x j : ℂ) := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose W,
      show star W * Bᴴ * (B * W) = star W * (Bᴴ * B) * W by simp only [Matrix.mul_assoc], h]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨Q, hQ, hBW⟩ := exists_unitary_of_gram hk (B * W) x hx hg
  rw [← hR W hW B, hBW, hL Q hQ]

/-- `F` agrees on matrices whose Gram matrices are unitarily similar and positive definite. -/
theorem F_gram {M k : ℕ} (hk : k ≤ M) (F : (Fin M → Fin k → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G)
    (A B : Matrix (Fin M) (Fin k) ℂ) {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ)
    (h : Aᴴ * A = V * (Bᴴ * B) * star V) (hpd : (Bᴴ * B).PosDef) : F A = F B := by
  have hH := hpd.isHermitian
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU : (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) ∈ unitaryGroup (Fin k) ℂ :=
    hH.eigenvectorUnitary.2
  have hd : (RCLike.ofReal ∘ hH.eigenvalues : Fin k → ℂ) = fun j => ((hH.eigenvalues j : ℝ) : ℂ) := rfl
  rw [hd] at hspec
  have hpos : ∀ j, 0 < hH.eigenvalues j := fun j => hpd.eigenvalues_pos j
  obtain ⟨U, hU, x, hx, hs⟩ : ∃ U ∈ unitaryGroup (Fin k) ℂ, ∃ x : Fin k → ℝ, (∀ j, 0 < x j) ∧
      Bᴴ * B = U * diagonal (fun j => (x j : ℂ)) * star U := ⟨_, hU, _, hpos, hspec⟩
  rw [F_emb hk F hL hR B hU x hx hs,
    F_emb hk F hL hR A (Submonoid.mul_mem _ hV hU) x hx ?_]
  rw [h, hs, star_mul]
  simp only [Matrix.mul_assoc]

/-- Unit phase of a complex number. -/
noncomputable def ph (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem ph_mul_norm (z : ℂ) : ph z * (‖z‖ : ℂ) = z := by
  unfold ph
  split_ifs with h
  · simp [h]
  · have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [div_mul_cancel₀ _ h2]

theorem star_ph_mul_norm (z : ℂ) : star (ph z) * (‖z‖ : ℂ) = star z := by
  have h := congrArg star (ph_mul_norm z)
  rwa [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] at h

theorem ph_mul_star (z : ℂ) : ph z * star (ph z) = 1 := by
  unfold ph
  split_ifs with h
  · simp
  · have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h1
    rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

/-- The phase matrix `diag(ph u_0, ..., ph u_{n-1}, 1)`. -/
noncomputable def Dm {n : ℕ} (u : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  diagonal (Fin.snoc (α := fun _ => ℂ) (fun i => ph (u i)) 1)

theorem Dm_mem {n : ℕ} (u : Fin n → ℂ) : Dm u ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff, Dm, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simpa using ph_mul_star (u i)

theorem Emb_castLE {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (i j : Fin n) :
    Emb M n μ (Fin.castLE h i) j = if i = j then ((Real.sqrt (μ j) : ℝ) : ℂ) else 0 := by
  unfold Emb
  simp only [Fin.val_castLE]
  by_cases hij : i = j
  · subst hij; simp
  · have : ¬ ((i : ℕ) = j) := fun e => hij (Fin.ext e)
    simp [this, hij]

theorem Emb_row_ge {M n : ℕ} (μ : Fin n → ℝ) (m : Fin M) (hm : n ≤ (m : ℕ)) (j : Fin n) :
    Emb M n μ m j = 0 := by
  unfold Emb
  have : ¬ ((m : ℕ) = j) := by omega
  simp [this]

theorem sum_Emb_col {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (i : Fin n) (f : Fin M → ℂ) :
    ∑ m, star (Emb M n μ m i) * f m = ((Real.sqrt (μ i) : ℝ) : ℂ) * f (Fin.castLE h i) := by
  rw [Finset.sum_eq_single (Fin.castLE h i)]
  · rw [Emb_castLE h μ i i, if_pos rfl, Complex.star_def, Complex.conj_ofReal]
  · intro m _ hm
    have : ¬ ((m : ℕ) = i) := fun e => hm (Fin.ext (by simpa using e))
    simp [Emb, this]
  · simp

theorem sum_col_Emb {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (j : Fin n) (f : Fin M → ℂ) :
    ∑ m, f m * Emb M n μ m j = f (Fin.castLE h j) * ((Real.sqrt (μ j) : ℝ) : ℂ) := by
  rw [Finset.sum_eq_single (Fin.castLE h j)]
  · rw [Emb_castLE h μ j j, if_pos rfl]
  · intro m _ hm
    have : ¬ ((m : ℕ) = j) := fun e => hm (Fin.ext (by simpa using e))
    simp [Emb, this]
  · simp

/-- Gram matrix of the bordered array. -/
theorem gram_join {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (g : Fin M → ℂ) :
    (Matrix.of (join (Emb M n μ) g))ᴴ *
        (Matrix.of (join (Emb M n μ) g)) =
      Dm (fun i => g (Fin.castLE h i)) *
        arrowC μ (fun i => Real.sqrt (μ i) * ‖g (Fin.castLE h i)‖) (∑ m, ‖g m‖ ^ 2) *
        star (Dm (fun i => g (Fin.castLE h i))) := by
  have hE := gram_Emb h μ hμ
  ext a b
  rw [Dm, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul,
    Matrix.mul_apply]
  simp only [conjTranspose_apply, arrowC, Matrix.map_apply, Pi.star_apply, Matrix.of_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      simp only [join, Fin.snoc_last, arrowR_ll, star_one, one_mul, mul_one]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    | cast j =>
      simp only [join, Fin.snoc_last, Fin.snoc_castSucc, arrowR_lc, one_mul]
      rw [sum_col_Emb h μ j (fun m => star (g m))]
      push_cast
      rw [mul_assoc, mul_comm (((‖g (Fin.castLE h j)‖ : ℝ)) : ℂ), star_ph_mul_norm, mul_comm]
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      simp only [join, Fin.snoc_last, Fin.snoc_castSucc, arrowR_cl, star_one,
        mul_one]
      rw [sum_Emb_col h μ i g]
      push_cast
      rw [mul_left_comm, ph_mul_norm]
    | cast j =>
      simp only [join, Fin.snoc_castSucc, arrowR_cc]
      have hij := congrFun (congrFun hE i) j
      rw [Matrix.mul_apply] at hij
      simp only [conjTranspose_apply] at hij
      rw [hij]
      by_cases hh : i = j
      · subst hh
        simp only [diagonal_apply_eq]
        rw [mul_comm, ← mul_assoc, mul_comm (star _), ph_mul_star, one_mul]
      · simp [diagonal_apply_ne _ hh]

/-- The bordered array has positive definite Gram matrix when `μ > 0` and `g_n ≠ 0`. -/
theorem posDef_join {M n : ℕ} (h : n + 1 ≤ M) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) (g : Fin M → ℂ)
    (hg : g ⟨n, by omega⟩ ≠ 0) :
    ((Matrix.of (join (Emb M n μ) g))ᴴ *
        (Matrix.of (join (Emb M n μ) g))).PosDef := by
  set A := Matrix.of (join (Emb M n μ) g) with hA
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_self _) fun x hx => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, dotProduct_star_self_pos_iff]
  intro hAx
  have hrow : ∀ m, ∑ j : Fin n, Emb M n μ m j * x (Fin.castSucc j) + g m * x (Fin.last n) = 0 := by
    intro m
    have := congrFun hAx m
    rw [mulVec, dotProduct, Fin.sum_univ_castSucc] at this
    simpa [hA, join] using this
  have hlast : x (Fin.last n) = 0 := by
    have := hrow ⟨n, by omega⟩
    rw [Finset.sum_eq_zero fun j _ => by rw [Emb_row_ge μ _ (le_refl n), zero_mul], zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left hg
  have hcs : ∀ i : Fin n, x (Fin.castSucc i) = 0 := by
    intro i
    have := hrow (Fin.castLE (by omega) i)
    simp only [Emb_castLE, hlast, mul_zero, add_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    have hs : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (hμ i)).ne'
    exact (mul_eq_zero.mp this).resolve_left hs
  apply hx
  funext j
  induction j using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hcs i

end SWL302

-- ===== from S3.lean =====

/-! S3: the normal form `N0 μ r s` of the bordered array and the two evaluations
`F (join (Emb μ) g) = F (N0 μ (rv g) (sv g))` (when `g_n ≠ 0`) and
`F (N0 μ r s) = F (Emb λ)` at the Dixon-Anderson point. Needs prefix + d80e94b4.lean + S1 + S2. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- Split `Fin M` into the first `n` and the remaining `M - n` indices. -/
def spl {M n : ℕ} (h : n ≤ M) : Fin M ≃ Fin n ⊕ Fin (M - n) :=
  (finCongr (by omega : M = n + (M - n))).trans finSumFinEquiv.symm

theorem spl_symm_inl {M n : ℕ} (h : n ≤ M) (a : Fin n) : (spl h).symm (Sum.inl a) = Fin.castLE h a := by
  apply Fin.ext; simp [spl]

theorem spl_castLE {M n : ℕ} (h : n ≤ M) (a : Fin n) : spl h (Fin.castLE h a) = Sum.inl a := by
  rw [← spl_symm_inl h a, Equiv.apply_symm_apply]

theorem spl_symm_inr_val {M n : ℕ} (h : n ≤ M) (b : Fin (M - n)) :
    (((spl h).symm (Sum.inr b) : Fin M) : ℕ) = n + b := by
  simp [spl]

theorem spl_n {M n : ℕ} (h : n + 1 ≤ M) :
    spl (by omega : n ≤ M) ⟨n, by omega⟩ = Sum.inr ⟨0, by omega⟩ := by
  apply (spl (by omega : n ≤ M)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [spl_symm_inr_val]
  simp

theorem sum_spl {M n : ℕ} (h : n ≤ M) (f : Fin M → ℝ) :
    ∑ m, f m = ∑ a : Fin n, f (Fin.castLE h a) + ∑ b : Fin (M - n), f ((spl h).symm (Sum.inr b)) := by
  rw [← Equiv.sum_comp (spl h).symm, Fintype.sum_sum_type]
  simp only [spl_symm_inl]

/-- The normal-form border column `(√r_0, ..., √r_{n-1}, √s, 0, ..., 0)`. -/
noncomputable def g0 {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) : Fin M → ℂ :=
  fun m => Sum.elim (fun a => ((Real.sqrt (r a) : ℝ) : ℂ))
    (fun b : Fin (M - n) => if (b : ℕ) = 0 then ((Real.sqrt s : ℝ) : ℂ) else 0) (spl h m)

/-- The normal form of the bordered array. -/
noncomputable def N0 {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (r : Fin n → ℝ) (s : ℝ) :
    Fin M → Fin (n + 1) → ℂ :=
  join (Emb M n μ) (g0 h r s)

theorem g0_castLE {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) (a : Fin n) :
    g0 h r s (Fin.castLE h a) = ((Real.sqrt (r a) : ℝ) : ℂ) := by
  simp [g0, spl_castLE]

theorem norm_g0_castLE {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) (a : Fin n) :
    ‖g0 h r s (Fin.castLE h a)‖ = Real.sqrt (r a) := by
  rw [g0_castLE, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem sum_norm_g0 {M n : ℕ} (h : n + 1 ≤ M) (r : Fin n → ℝ) (hr : ∀ a, 0 ≤ r a) (s : ℝ) (hs : 0 ≤ s) :
    ∑ m, ‖g0 (by omega : n ≤ M) r s m‖ ^ 2 = ∑ a, r a + s := by
  have h' : n ≤ M := by omega
  rw [sum_spl h']
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_g0_castLE, Real.sq_sqrt (hr a)]
  · have hp : 0 < M - n := by omega
    rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin (M - n))]
    · simp [g0, Real.sq_sqrt hs, abs_of_nonneg (Real.sqrt_nonneg s)]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun e => hb (Fin.ext e)
      simp [g0, this]
    · simp

theorem g0_n {M n : ℕ} (h : n + 1 ≤ M) (r : Fin n → ℝ) (s : ℝ) :
    g0 (by omega : n ≤ M) r s ⟨n, by omega⟩ = ((Real.sqrt s : ℝ) : ℂ) := by
  simp [g0, spl_n h]

/-- Border data of a column. -/
noncomputable def rv {M n : ℕ} (h : n ≤ M) (g : Fin M → ℂ) : Fin n → ℝ :=
  fun a => ‖g (Fin.castLE h a)‖ ^ 2

noncomputable def sv {M n : ℕ} (h : n ≤ M) (g : Fin M → ℂ) : ℝ :=
  ∑ b : Fin (M - n), ‖g ((spl h).symm (Sum.inr b))‖ ^ 2

theorem sv_pos {M n : ℕ} (h : n + 1 ≤ M) (g : Fin M → ℂ) (hg : g ⟨n, by omega⟩ ≠ 0) :
    0 < sv (by omega : n ≤ M) g := by
  have hp : 0 < M - n := by omega
  unfold sv
  have hb : (spl (by omega : n ≤ M)).symm (Sum.inr ⟨0, hp⟩) = ⟨n, by omega⟩ := by
    rw [← spl_n h, Equiv.symm_apply_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b _ => sq_nonneg ‖g ((spl _).symm (Sum.inr b))‖)
    (Finset.mem_univ (⟨0, hp⟩ : Fin (M - n))))
  rw [hb]
  exact pow_pos (norm_pos_iff.mpr hg) 2

/-- The bordered array and its normal form have the same invariant. -/
theorem F_join_eq_N0 {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) (g : Fin M → ℂ) (hg : g ⟨n, by omega⟩ ≠ 0) :
    F (join (Emb M n μ) g) = F (N0 (by omega : n ≤ M) μ (rv (by omega : n ≤ M) g) (sv (by omega : n ≤ M) g)) := by
  have h' : n ≤ M := by omega
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => (hμ i).le
  have hr : ∀ a, 0 ≤ rv h' g a := fun a => sq_nonneg _
  have hs := sv_pos h g hg
  set u : Fin n → ℂ := fun i => g (Fin.castLE h' i)
  set u0 : Fin n → ℂ := fun i => g0 h' (rv h' g) (sv h' g) (Fin.castLE h' i)
  have hX : arrowC μ (fun i => Real.sqrt (μ i) * ‖g0 h' (rv h' g) (sv h' g) (Fin.castLE h' i)‖)
        (∑ m, ‖g0 h' (rv h' g) (sv h' g) m‖ ^ 2) =
      arrowC μ (fun i => Real.sqrt (μ i) * ‖g (Fin.castLE h' i)‖) (∑ m, ‖g m‖ ^ 2) := by
    congr 1
    · funext i
      rw [norm_g0_castLE, rv, Real.sqrt_sq (norm_nonneg _)]
    · rw [sum_norm_g0 h _ hr _ hs.le, sum_spl h' (fun m => ‖g m‖ ^ 2)]
      rfl
  have hA := gram_join h' μ hμ0 g
  have hB := gram_join h' μ hμ0 (g0 h' (rv h' g) (sv h' g))
  rw [hX] at hB
  have hD0 : star (Dm u0) * Dm u0 = 1 := mem_unitaryGroup_iff'.mp (Dm_mem u0)
  have hpd := posDef_join h μ hμ (g0 h' (rv h' g) (sv h' g))
    (by rw [g0_n h]; exact_mod_cast (Real.sqrt_pos.mpr hs).ne')
  refine F_gram h F hL hR (Matrix.of (join (Emb M n μ) g)) (Matrix.of (N0 h' μ (rv h' g) (sv h' g)))
    (V := Dm u * star (Dm u0)) (Submonoid.mul_mem _ (Dm_mem u) (Unitary.star_mem (Dm_mem u0))) ?_ hpd
  unfold N0
  rw [hA, hB, star_mul, star_star]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (Dm u0)) (Dm u0), hD0, Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ (star (Dm u0)) (Dm u0), hD0, Matrix.mul_one]

/-- At the Dixon-Anderson point the normal form is unitarily equivalent to `Emb λ`. -/
theorem F_N0_eq_Emb {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ} (hla : la ∈ Ilace μ)
    (hlap : ∀ j, 0 < la j) (hs : 0 ≤ cv μ la - ∑ i, wv μ la i / μ i) :
    F (N0 (by omega : n ≤ M) μ (fun i => wv μ la i / μ i) (cv μ la - ∑ i, wv μ la i / μ i)) =
      F (Emb M (n + 1) la) := by
  have h' : n ≤ M := by omega
  set r : Fin n → ℝ := fun i => wv μ la i / μ i with hrdef
  set s := cv μ la - ∑ i, wv μ la i / μ i with hsdef
  have hw : ∀ i, 0 < wv μ la i := fun i => wv_pos hla i
  have hr : ∀ a, 0 ≤ r a := fun a => (div_pos (hw a) (hμ a)).le
  obtain ⟨U, hU, hsim⟩ := arrowC_similar hla
  have hX : arrowC μ (fun i => Real.sqrt (μ i) * ‖g0 h' r s (Fin.castLE h' i)‖)
        (∑ m, ‖g0 h' r s m‖ ^ 2) = arrowC μ (fun i => Real.sqrt (wv μ la i)) (cv μ la) := by
    congr 1
    · funext i
      rw [norm_g0_castLE, ← Real.sqrt_mul (hμ i).le, hrdef, mul_div_cancel₀ _ (hμ i).ne']
    · rw [sum_norm_g0 h _ hr _ hs, hsdef]
      ring
  have hB := gram_join h' μ (fun i => (hμ i).le) (g0 h' r s)
  rw [hX, hsim] at hB
  set u0 : Fin n → ℂ := fun i => g0 h' r s (Fin.castLE h' i)
  refine F_emb h F hL hR (Matrix.of (N0 h' μ r s)) (W := Dm u0 * U)
    (Submonoid.mul_mem _ (Dm_mem u0) hU) la hlap ?_
  unfold N0
  rw [hB, star_mul]
  simp only [Matrix.mul_assoc]

end SWL302

-- ===== from S4.lean =====

/-! S4: the sum of `a + 1` i.i.d. `Exp(1)` variables has the Gamma density `x^a e^{-x} / a!`.
Needs prefix (W5a: dexp, exp1; W5c: mp_lastSplit). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set SpikedWishart.Separated.Lib.Weyl

/-- Gamma density with integer shape `a + 1`. -/
noncomputable def dgam (a : ℕ) (x : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => x ^ a * Real.exp (-x) / (a.factorial : ℝ)) x

theorem measurable_dgam (a : ℕ) : Measurable (dgam a) := by
  unfold dgam
  exact (by fun_prop : Measurable fun x : ℝ => x ^ a * Real.exp (-x) / (a.factorial : ℝ)).indicator
    measurableSet_Ioi

theorem dgam_zero (x : ℝ) : dgam 0 x = dexp x := by
  simp [dgam, dexp]

theorem lintegral_exp1 (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂exp1 = ∫⁻ x, Φ x * ENNReal.ofReal (dexp x) := by
  rw [exp1, lintegral_withDensity_eq_lintegral_mul _ measurable_dexp.ennreal_ofReal hΦ]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  ring

/-- Convolution of the Gamma(a+1) density with Exp(1). -/
theorem conv_dgam (a : ℕ) (y : ℝ) :
    ∫⁻ x, ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) = ENNReal.ofReal (dgam (a + 1) y) := by
  have hpt : ∀ x, ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) =
      (Ioo 0 y).indicator (fun x => ENNReal.ofReal (x ^ a * (Real.exp (-y) / (a.factorial : ℝ)))) x := by
    intro x
    by_cases hx0 : 0 < x
    · by_cases hxy : x < y
      · have hm : x ∈ Ioo 0 y := ⟨hx0, hxy⟩
        have hyx : y - x ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
        rw [indicator_of_mem hm, dgam, dexp, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx0),
          indicator_of_mem hyx, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Real.exp (-x) * Real.exp (-(y - x)) = Real.exp (-y) := by
          rw [← Real.exp_add]; ring_nf
        calc x ^ a * Real.exp (-x) / (a.factorial : ℝ) * Real.exp (-(y - x))
            = x ^ a * (Real.exp (-x) * Real.exp (-(y - x))) / (a.factorial : ℝ) := by ring
          _ = _ := by rw [this]; ring
      · have hm : x ∉ Ioo 0 y := fun h => hxy h.2
        have hyx : y - x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
        rw [indicator_of_notMem hm, dexp, indicator_of_notMem hyx]
        simp
    · have hm : x ∉ Ioo 0 y := fun h => hx0 h.1
      rw [indicator_of_notMem hm, dgam, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx0)]
      simp
  rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioo]
  by_cases hy : 0 < y
  · have hint : IntegrableOn (fun x : ℝ => x ^ a * (Real.exp (-y) / (a.factorial : ℝ))) (Ioo 0 y) :=
      (by fun_prop : Continuous fun x : ℝ => x ^ a * (Real.exp (-y) / (a.factorial : ℝ))).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy.le,
        intervalIntegral.integral_mul_const, integral_pow]
      rw [dgam, indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      have : 0 < x := hx.1
      simp only [Pi.zero_apply]
      positivity
  · rw [Ioo_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure, dgam,
      indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy), ENNReal.ofReal_zero]

/-- The sum of `a + 1` i.i.d. `Exp(1)` variables has density `dgam a`. -/
theorem lintegral_sum_exp1 (a : ℕ) (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ v, Φ (∑ b, v b) ∂(Measure.pi fun _ : Fin (a + 1) => exp1) =
      ∫⁻ x, Φ x * ENNReal.ofReal (dgam a x) := by
  have := isProb_exp1
  induction a generalizing Φ with
  | zero =>
    have h := measurePreserving_funUnique exp1 (Fin 1)
    have e : (fun v : Fin 1 → ℝ => Φ (∑ b, v b)) = Φ ∘ (MeasurableEquiv.funUnique (Fin 1) ℝ) := by
      funext v; simp [Fin.sum_univ_one]
    rw [e]
    refine (h.lintegral_comp hΦ).trans ?_
    rw [lintegral_exp1 Φ hΦ]
    simp only [dgam_zero]
  | succ a ih =>
    have h := mp_lastSplit exp1 (a + 1)
    have e : (fun v : Fin (a + 2) → ℝ => Φ (∑ b, v b)) =
        (fun p : ℝ × (Fin (a + 1) → ℝ) => Φ (p.1 + ∑ j, p.2 j)) ∘
          (fun r : Fin (a + 2) → ℝ => (r (Fin.last (a + 1)), fun j : Fin (a + 1) => r (Fin.castSucc j))) := by
      funext v; simp only [Function.comp_apply, Fin.sum_univ_castSucc]; rw [add_comm]
    have hm2 : Measurable (fun p : ℝ × (Fin (a + 1) → ℝ) => Φ (p.1 + ∑ j, p.2 j)) :=
      hΦ.comp (measurable_fst.add (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd))
    rw [e]
    refine (h.lintegral_comp hm2).trans ?_
    rw [lintegral_prod _ hm2.aemeasurable]
    have h1 : ∀ t : ℝ, ∫⁻ w, Φ (t + ∑ j, w j) ∂(Measure.pi fun _ : Fin (a + 1) => exp1) =
        ∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x) :=
      fun t => ih (fun x => Φ (t + x)) (hΦ.comp (measurable_const.add measurable_id))
    simp only [h1]
    have hj : Measurable (fun q : ℝ × ℝ => Φ (q.1 + q.2) * ENNReal.ofReal (dgam a q.2)) :=
      (hΦ.comp (measurable_fst.add measurable_snd)).mul
        ((measurable_dgam a).ennreal_ofReal.comp measurable_snd)
    rw [lintegral_exp1 _ (hj.lintegral_prod_right')]
    have hD : Measurable (fun x : ℝ => ENNReal.ofReal (dexp x)) := measurable_dexp.ennreal_ofReal
    have hG : Measurable (fun x : ℝ => ENNReal.ofReal (dgam a x)) := (measurable_dgam a).ennreal_ofReal
    calc ∫⁻ t, (∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x)) * ENNReal.ofReal (dexp t)
        = ∫⁻ t, ∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t) := by
          refine lintegral_congr fun t => (lintegral_mul_const _ ?_).symm
          exact (hΦ.comp (measurable_const.add measurable_id)).mul hG
      _ = ∫⁻ x, ∫⁻ t, Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t) := by
          refine lintegral_lintegral_swap ?_
          exact (((hΦ.comp (measurable_fst.add measurable_snd)).mul (hG.comp measurable_snd)).mul
            (hD.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ∫⁻ y, Φ y * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_sub_right_eq_self
            (fun t => Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t)) x]
          simp only [sub_add_cancel]
      _ = ∫⁻ y, ∫⁻ x, Φ y * (ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x))) := by
          rw [lintegral_lintegral_swap]
          · refine lintegral_congr fun y => lintegral_congr fun x => ?_
            ring
          · exact (((hΦ.comp measurable_snd).mul (hG.comp measurable_fst)).mul
              (hD.comp (measurable_snd.sub measurable_fst))).aemeasurable
      _ = ∫⁻ y, Φ y * ENNReal.ofReal (dgam (a + 1) y) := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable (fun x : ℝ => ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x))) :=
            hG.mul (hD.comp (measurable_const.sub measurable_id))
          rw [lintegral_const_mul _ hm, conv_dgam]

end SWL302

-- ===== from S5.lean =====

/-! S5: the law of the border data `(rv g, sv g)` under `cgv M`: `Exp(1)^n ⊗ Gamma(M - n)`.
Needs prefix + d80e94b4.lean + S1..S4. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set SpikedWishart.Separated.Lib.Weyl

theorem pi_split_mp {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun v : ι → X => ((fun a => v (e.symm (Sum.inl a))),
        (fun b => v (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : α ⊕ β => X) (fun _ => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => X) (fun _ => μ)
  have h := h2.comp h1
  convert h using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
  ext a
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

theorem lintegral_sum_exp1' (p : ℕ) (hp : 0 < p) (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ v, Φ (∑ b, v b) ∂(Measure.pi fun _ : Fin p => exp1) =
      ∫⁻ x, Φ x * ENNReal.ofReal (dgam (p - 1) x) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  simpa using lintegral_sum_exp1 a Φ hΦ

/-- Law of the border data. -/
theorem lintegral_border {M n : ℕ} (h : n + 1 ≤ M) (Ψ : (Fin n → ℝ) × ℝ → ENNReal) (hΨ : Measurable Ψ) :
    ∫⁻ g, Ψ (rv (by omega : n ≤ M) g, sv (by omega : n ≤ M) g) ∂(cgv M) =
      ∫⁻ r, (∫⁻ x, Ψ (r, x) * ENNReal.ofReal (dgam (M - n - 1) x)) ∂(Measure.pi fun _ : Fin n => exp1) := by
  have h' : n ≤ M := by omega
  have := isProb_cg
  have := isProb_exp1
  have hsplit := pi_split_mp SpikedWishart.SoftEdge.stdComplexGaussian (spl h')
  have hns := (mp_normSqvec n).prod (mp_normSqvec (M - n))
  have hcomp := hns.comp hsplit
  have hsum : Measurable (fun q : (Fin n → ℝ) × (Fin (M - n) → ℝ) => Ψ (q.1, ∑ b, q.2 b)) :=
    hΨ.comp (measurable_fst.prodMk (Finset.measurable_sum _ fun b _ => (measurable_pi_apply b).comp measurable_snd))
  have e : ∀ g : Fin M → ℂ, Ψ (rv h' g, sv h' g) =
      (fun q : (Fin n → ℝ) × (Fin (M - n) → ℝ) => Ψ (q.1, ∑ b, q.2 b))
        (((fun p : (Fin n → ℂ) × (Fin (M - n) → ℂ) =>
          ((fun i => Complex.normSq (p.1 i)), (fun i => Complex.normSq (p.2 i)))))
          ((fun a => g ((spl h').symm (Sum.inl a))), (fun b => g ((spl h').symm (Sum.inr b))))) := by
    intro g
    simp only [sv, spl_symm_inl, Complex.normSq_eq_norm_sq]
    rfl
  simp_rw [e]
  refine (hcomp.lintegral_comp hsum).trans ?_
  rw [lintegral_prod _ hsum.aemeasurable]
  refine lintegral_congr fun r => ?_
  exact lintegral_sum_exp1' (M - n) (by omega) (fun x => Ψ (r, x)) (hΨ.comp (measurable_const.prodMk measurable_id))

end SWL302

-- ===== from S6.lean =====

/-! S6: the border average at a positive diagonal array, `hW F (Emb μ)`, by the Dixon-Anderson
change of variables (Laguerre version). Needs prefix + d80e94b4.lean + S1..S5. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

theorem cg_zero : SpikedWishart.SoftEdge.stdComplexGaussian {0} = 0 := by
  have h2 : exp1 {0} = 0 := by
    unfold exp1
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ Real.volume_singleton
  rw [← map_normSq_cg, Measure.map_apply Complex.continuous_normSq.measurable
    (measurableSet_singleton 0)] at h2
  refine measure_mono_null (fun z hz => ?_) h2
  simp only [Set.mem_singleton_iff] at hz
  simp [hz]

theorem ae_ne_zero {M n : ℕ} (h : n + 1 ≤ M) : ∀ᵐ g ∂(cgv M), g ⟨n, by omega⟩ ≠ 0 := by
  rw [ae_iff]
  have e : {g : Fin M → ℂ | ¬ g ⟨n, by omega⟩ ≠ 0} = Function.eval (⟨n, by omega⟩ : Fin M) ⁻¹' {0} := by
    ext g; simp
  rw [e]
  have h0 : stdComplexGaussian ({0} : Set ℂ) = 0 := cg_zero
  exact Measure.pi_eval_preimage_null _ h0

/-- `c - Σ w_i / μ_i = ∏ λ / ∏ μ` (the Dixon-Anderson identity at `t = 0`). -/
theorem prod_identity {n : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ}
    (hla : la ∈ Ilace μ) :
    cv μ la - ∑ i, wv μ la i / μ i = (∏ j, la j) / ∏ i, μ i := by
  have hinj := (ilace_mu_strictAnti hla).injective
  have h0 : ∏ j, (0 - la j) = Rf μ (wv μ la) (cv μ la) 0 := poly_id_eval hinj la 0
  rw [Rf_eq_prod_sec μ (wv μ la) (cv μ la) 0 (fun i => (hμ i).ne)] at h0
  unfold sec at h0
  simp only [zero_sub, Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h0
  have hs : ∑ i, wv μ la i / -μ i = -∑ i, wv μ la i / μ i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => div_neg _
  rw [hs] at h0
  have hP : (∏ i, μ i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hμ i).ne'
  rw [eq_div_iff hP]
  have hpm : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : (-1 : ℝ) ^ n * ((cv μ la - ∑ i, wv μ la i / μ i) * ∏ i, μ i) = (-1) ^ n * ∏ j, la j := by
    linear_combination h0
  exact mul_left_cancel₀ hpm h1

theorem continuous_g0 {M n : ℕ} (h : n ≤ M) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => g0 h p.1 p.2) := by
  refine continuous_pi fun m => ?_
  unfold g0
  generalize spl h m = q
  rcases q with a | b
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; split_ifs <;> fun_prop

theorem continuous_N0 {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => N0 h μ p.1 p.2) := by
  unfold N0
  exact (continuous_join M n).comp (continuous_const.prodMk (continuous_g0 h))

/-- Iterated `Exp(1)^n ⊗ (density D)` integral as a Lebesgue integral on `ℝ^{n+1}`. -/
theorem lintegral_exp_dens {n : ℕ} (D : ℝ → ℝ) (hD : Measurable D)
    (Ψ : (Fin n → ℝ) × ℝ → ENNReal) (hΨ : Measurable Ψ) :
    ∫⁻ r, (∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x)) ∂(Measure.pi fun _ : Fin n => exp1) =
      ∫⁻ y : Fin (n + 1) → ℝ, Ψ (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * D (y (Fin.last n))) := by
  have hDw : Measurable (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) :=
    Finset.measurable_prod _ (fun i _ => measurable_dexp.ennreal_ofReal.comp (measurable_pi_apply i))
  have hf : Measurable (fun p : (Fin n → ℝ) × ℝ => Ψ p * ENNReal.ofReal (D p.2)) :=
    hΨ.mul (hD.ennreal_ofReal.comp measurable_snd)
  have hin : Measurable (fun r : Fin n → ℝ => ∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x)) :=
    hf.lintegral_prod_right'
  have hM : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      (∏ i, ENNReal.ofReal (dexp (p.1 i))) * (Ψ p * ENNReal.ofReal (D p.2))) :=
    (hDw.comp measurable_fst).mul hf
  rw [pi_exp1, lintegral_withDensity_eq_lintegral_mul _ hDw hin]
  have e1 : ∫⁻ r, ((fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) *
      (fun r : Fin n → ℝ => ∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x))) r =
      ∫⁻ p : (Fin n → ℝ) × ℝ, (∏ i, ENNReal.ofReal (dexp (p.1 i))) * (Ψ p * ENNReal.ofReal (D p.2))
        ∂((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := by
    rw [lintegral_prod _ hM.aemeasurable]
    refine lintegral_congr fun r => ?_
    rw [Pi.mul_apply]
    exact (lintegral_const_mul _ (hf.comp measurable_prodMk_left)).symm
  rw [e1, ← lintegral_prod_swap]
  have h := mp_lastSplit (volume : Measure ℝ) n
  refine Eq.trans (h.lintegral_comp (hM.comp measurable_swap)).symm ?_
  refine lintegral_congr (fun y => ?_)
  simp only [Function.comp_apply, Prod.swap]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => dexp_nonneg _)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => dexp_nonneg _)]
  rw [show Fin.init y = fun j => y j.castSucc from rfl]
  ring

/-- `d = (μ, 1)`. -/
noncomputable def dvec {n : ℕ} (μ : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) μ 1

/-- The lower-triangular map `(r, s) ↦ (μ r, s + Σ r)`. -/
noncomputable def Tm {n : ℕ} (μ : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = j then dvec μ i else if i = Fin.last n then 1 else 0

theorem det_Tm {n : ℕ} (μ : Fin n → ℝ) : (Tm μ).det = ∏ i, μ i := by
  rw [det_of_isLowerTriangular _ ?_]
  · simp only [Tm, if_true]
    rw [Fin.prod_univ_castSucc]
    simp [dvec]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Tm]
    rw [if_neg (ne_of_lt hij'), if_neg]
    intro hi
    rw [hi] at hij'
    exact absurd hij' (not_lt.mpr (Fin.le_last j))

theorem Tm_mulVec_cs {n : ℕ} (μ : Fin n → ℝ) (y : Fin (n + 1) → ℝ) (i : Fin n) :
    (Tm μ *ᵥ y) i.castSucc = μ i * y i.castSucc := by
  simp only [mulVec, dotProduct, Tm]
  rw [Finset.sum_eq_single i.castSucc]
  · simp [dvec]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), if_neg (Fin.castSucc_ne_last i)]
    simp
  · simp

theorem Tm_mulVec_last {n : ℕ} (μ : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    (Tm μ *ᵥ y) (Fin.last n) = y (Fin.last n) + ∑ i : Fin n, y i.castSucc := by
  simp only [mulVec, dotProduct, Tm]
  rw [Fin.sum_univ_castSucc]
  have hne : ∀ i : Fin n, (Fin.last n = i.castSucc) = False :=
    fun i => eq_false (Fin.castSucc_ne_last i).symm
  simp [dvec, hne, add_comm]

theorem lintegral_Tm {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (G : (Fin (n + 1) → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ y, G (Tm μ *ᵥ y) = ENNReal.ofReal (∏ i, μ i)⁻¹ * ∫⁻ z, G z := by
  have hP : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hμ i
  have hdet : LinearMap.det (Matrix.toLin' (Tm μ)) ≠ 0 := by
    rw [LinearMap.det_toLin', det_Tm]; exact hP.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin (n + 1) → ℝ)) hdet
  rw [LinearMap.det_toLin', det_Tm, abs_of_pos (inv_pos.mpr hP)] at hmap
  have hc : Measurable (Matrix.toLin' (Tm μ)) := (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ y, G (Tm μ *ᵥ y) = ∫⁻ y, G (Matrix.toLin' (Tm μ) y) := by simp only [Matrix.toLin'_apply]
    _ = ∫⁻ z, G z ∂(Measure.map (Matrix.toLin' (Tm μ)) volume) := (lintegral_map hG hc).symm
    _ = _ := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

end SWL302

-- ===== from S6c.lean =====

/-! S6c: the border average at a positive diagonal array, `hW F (Emb μ)`, by the Dixon-Anderson
change of variables (Laguerre version). Needs prefix + d80e94b4.lean + S1..S6. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- The new Laguerre factor, supported on `λ_n > 0`. -/
noncomputable def wt {n : ℕ} (a : ℕ) (la : Fin (n + 1) → ℝ) : ℝ :=
  if 0 < la (Fin.last n) then Real.exp (-∑ j, la j) * (∏ j, la j) ^ a else 0

theorem ilace_pos {n : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ}
    (hla : la ∈ Ilace μ) (i : Fin n) : 0 < la i.castSucc :=
  (hμ i).trans (hla i).1

theorem ofReal_eq_helper (p1 p2 p3 q1 q2 q3 : ℝ) (f : ENNReal) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (h : p1 * (p2 * p3) = q1 * (q2 * q3)) :
    ENNReal.ofReal p1 * (ENNReal.ofReal p2 * (f * ENNReal.ofReal p3)) =
      ENNReal.ofReal q1 * (ENNReal.ofReal q2 * f * ENNReal.ofReal q3) := by
  have e1 : ENNReal.ofReal p1 * (ENNReal.ofReal p2 * (f * ENNReal.ofReal p3)) =
      ENNReal.ofReal (p1 * (p2 * p3)) * f := by
    rw [ENNReal.ofReal_mul hp1, ENNReal.ofReal_mul hp2]; ring
  have e2 : ENNReal.ofReal q1 * (ENNReal.ofReal q2 * f * ENNReal.ofReal q3) =
      ENNReal.ofReal (q1 * (q2 * q3)) * f := by
    rw [ENNReal.ofReal_mul hq1, ENNReal.ofReal_mul hq2]; ring
  rw [e1, e2, h]

/-- The border average at `Emb μ`, `μ` strictly decreasing and positive. -/
theorem hW_diag {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    {μ : Fin n → ℝ} (hanti : StrictAnti μ) (hμ : ∀ i, 0 < μ i) :
    hW F (Emb M n μ) = ENNReal.ofReal ((∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ /
        ((M - n - 1).factorial : ℝ)) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * F (Emb M (n + 1) la) *
        ENNReal.ofReal (wt (M - n - 1) la) := by
  have h' : n ≤ M := by omega
  have hMa : M - n = M - n - 1 + 1 := by omega
  set a := M - n - 1 with ha
  have hPμ : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hμ i
  set Ψ : (Fin n → ℝ) × ℝ → ENNReal := fun p => F (N0 h' μ p.1 p.2) with hΨdef
  have hΨ : Measurable Ψ := hFm.comp (continuous_N0 h' μ).measurable
  set G : (Fin (n + 1) → ℝ) → ENNReal := fun z =>
    Ψ (fun i => z i.castSucc / μ i, z (Fin.last n) - ∑ i, z i.castSucc / μ i) *
      ENNReal.ofReal ((∏ i, dexp (z i.castSucc / μ i)) *
        dgam a (z (Fin.last n) - ∑ i, z i.castSucc / μ i)) with hGdef
  have hr : Measurable (fun z : Fin (n + 1) → ℝ => fun i : Fin n => z i.castSucc / μ i) :=
    (by fun_prop : Continuous fun z : Fin (n + 1) → ℝ => fun i : Fin n => z i.castSucc / μ i).measurable
  have hs : Measurable (fun z : Fin (n + 1) → ℝ => z (Fin.last n) - ∑ i, z i.castSucc / μ i) :=
    (by fun_prop : Continuous fun z : Fin (n + 1) → ℝ =>
      z (Fin.last n) - ∑ i, z i.castSucc / μ i).measurable
  have hX : Measurable (fun z : Fin (n + 1) → ℝ => (∏ i, dexp (z i.castSucc / μ i)) *
      dgam a (z (Fin.last n) - ∑ i, z i.castSucc / μ i)) :=
    Measurable.mul (Finset.measurable_prod _ fun i _ =>
      measurable_dexp.comp ((measurable_pi_apply _).div_const _)) ((measurable_dgam a).comp hs)
  have hG : Measurable G := (hΨ.comp (hr.prodMk hs)).mul hX.ennreal_ofReal
  have step1 : hW F (Emb M n μ) = ∫⁻ g, Ψ (rv h' g, sv h' g) ∂(cgv M) := by
    unfold hW
    exact lintegral_congr_ae ((ae_ne_zero h).mono fun g hg => F_join_eq_N0 h F hL hR μ hμ g hg)
  have step2 := lintegral_border h Ψ hΨ
  have step3 := lintegral_exp_dens (dgam a) (measurable_dgam a) Ψ hΨ
  have step4 : ∫⁻ y : Fin (n + 1) → ℝ, Ψ (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * dgam a (y (Fin.last n))) =
      ∫⁻ y, G (Tm μ *ᵥ y) := by
    refine lintegral_congr fun y => ?_
    have e1 : ∀ i, (Tm μ *ᵥ y) i.castSucc / μ i = y i.castSucc := fun i => by
      rw [Tm_mulVec_cs, mul_div_cancel_left₀ _ (hμ i).ne']
    have e2 : (Tm μ *ᵥ y) (Fin.last n) - ∑ i : Fin n, y i.castSucc = y (Fin.last n) := by
      rw [Tm_mulVec_last, add_sub_cancel_right]
    rw [show Fin.init y = fun i => y i.castSucc from rfl]
    simp only [hGdef, e1, e2]
  have step5 := lintegral_Tm μ hμ G hG
  have hsupp : ∀ z, z ∉ Vpos n → G z = 0 := by
    intro z hz
    simp only [Vpos, Set.mem_setOf_eq, not_forall, not_lt] at hz
    obtain ⟨i, hi⟩ := hz
    have hd : dexp (z i.castSucc / μ i) = 0 := by
      unfold dexp
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      exact div_nonpos_of_nonpos_of_nonneg hi (hμ i).le
    have hp : ∏ j, dexp (z j.castSucc / μ j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hd
    simp only [hGdef, hp, zero_mul, ENNReal.ofReal_zero, mul_zero]
  have step6 : ∫⁻ z, G z = ∫⁻ z in Vpos n, G z := by
    rw [← lintegral_indicator (measurableSet_Vpos n)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Vpos n
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
  have step7 := lintegral_Vpos_eq hanti G
  rw [step1]
  refine step2.trans ?_
  rw [step3, step4, step5, step6, step7, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
  have hcs : ∀ i : Fin n, Phi μ la i.castSucc = wv μ la i := fun i => by
    simp only [Phi]; exact Fin.snoc_castSucc _ _ _
  have hlast : Phi μ la (Fin.last n) = cv μ la := by
    simp only [Phi]; exact Fin.snoc_last _ _
  have hP := prod_identity hμ hla
  have hlapos := fun i => ilace_pos hμ hla i
  have hprod : ∏ j, la j = (∏ i : Fin n, la i.castSucc) * la (Fin.last n) := Fin.prod_univ_castSucc _
  have hcsP : 0 < ∏ i : Fin n, la i.castSucc := Finset.prod_pos fun i _ => hlapos i
  have hK : 0 ≤ (∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ / ((a.factorial : ℕ) : ℝ) :=
    div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hPμ).le _) (Real.exp_pos _).le)
      (vdm_nonneg μ)) (Nat.cast_nonneg _)
  simp only [hGdef, hcs, hlast]
  by_cases hpos : 0 < la (Fin.last n)
  · have hlap : ∀ j, 0 < la j := by
      intro j
      induction j using Fin.lastCases with
      | last => exact hpos
      | cast i => exact hlapos i
    have hpl : 0 < ∏ j, la j := Finset.prod_pos fun j _ => hlap j
    have hPpos : 0 < (∏ j, la j) / ∏ i, μ i := div_pos hpl hPμ
    have hs0 : 0 ≤ cv μ la - ∑ i, wv μ la i / μ i := by rw [hP]; exact hPpos.le
    have hF' : Ψ (fun i => wv μ la i / μ i, cv μ la - ∑ i, wv μ la i / μ i) = F (Emb M (n + 1) la) :=
      F_N0_eq_Emb h F hL hR μ hμ hla hlap hs0
    rw [hF', hP]
    have hd : ∀ i, dexp (wv μ la i / μ i) = Real.exp (-(wv μ la i / μ i)) := fun i => by
      unfold dexp; rw [Set.indicator_of_mem]; exact div_pos (wv_pos hla i) (hμ i)
    have hg : dgam a ((∏ j, la j) / ∏ i, μ i) =
        ((∏ j, la j) / ∏ i, μ i) ^ a * Real.exp (-((∏ j, la j) / ∏ i, μ i)) / (a.factorial : ℝ) := by
      unfold dgam; exact Set.indicator_of_mem (show _ ∈ Ioi (0 : ℝ) from hPpos) _
    have hwt : wt a la = Real.exp (-∑ j, la j) * (∏ j, la j) ^ a := by rw [wt, if_pos hpos]
    simp only [hd, hg, hwt]
    rw [← Real.exp_sum]
    have hexp : Real.exp (∑ i, -(wv μ la i / μ i)) * Real.exp (-((∏ j, la j) / ∏ i, μ i)) =
        Real.exp (∑ i, μ i) * Real.exp (-∑ j, la j) := by
      rw [Finset.sum_neg_distrib, ← Real.exp_add, ← Real.exp_add]
      congr 1
      have hc := hP
      unfold cv at hc
      linarith
    refine ofReal_eq_helper _ _ _ _ _ _ _ (inv_pos.mpr hPμ).le
      (div_nonneg (vdm_nonneg la) (vdm_nonneg μ)) hK (vdm_nonneg la) ?_
    rw [hMa, div_pow]
    linear_combination ((∏ i, μ i)⁻¹ * (vdm la / vdm μ) * ((∏ j, la j) ^ a / (∏ i, μ i) ^ a) /
      (a.factorial : ℝ)) * hexp
  · have hwt : wt a la = 0 := by rw [wt, if_neg hpos]
    have hg0 : dgam a ((∏ j, la j) / ∏ i, μ i) = 0 := by
      unfold dgam
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      refine div_nonpos_of_nonpos_of_nonneg ?_ hPμ.le
      rw [hprod]
      exact mul_nonpos_iff.mpr (Or.inl ⟨hcsP.le, not_lt.mp hpos⟩)
    rw [hP, hg0, hwt]
    simp

end SWL302

-- ===== from S7.lean =====

/-! S7: the induction step of the array Weyl formula and the final assembly.
Needs prefix + d80e94b4.lean + S1..S6c. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

theorem vandSq_eq_vdm {k : ℕ} (x : Fin k → ℝ) : vandSq x = vdm x ^ 2 := by
  unfold vandSq vdm
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_filter]
  exact Finset.prod_congr (by ext j; simp) (fun j _ => (sq_abs _).symm)

theorem lag_perm {k : ℕ} (a : ℕ) (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    lag a (x ∘ σ) = lag a x := by
  unfold lag
  rw [vandSq_eq_vdm, vandSq_eq_vdm, vdm_perm]
  congr 1
  exact Equiv.prod_comp σ (fun j => Real.exp (-x j) * x j ^ a)

theorem lag_eq_vdm {k : ℕ} (a : ℕ) (x : Fin k → ℝ) :
    lag a x = vdm x ^ 2 * (Real.exp (-∑ j, x j) * (∏ j, x j) ^ a) := by
  unfold lag
  rw [vandSq_eq_vdm, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow, Finset.sum_neg_distrib]

theorem continuous_Emb (M k : ℕ) :
    Continuous (fun x : Fin k → ℝ => fun (m : Fin M) (j : Fin k) => Emb M k x m j) := by
  refine continuous_pi fun m => continuous_pi fun j => ?_
  show Continuous fun x : Fin k → ℝ => if (m : ℕ) = j then ((Real.sqrt (x j) : ℝ) : ℂ) else 0
  split_ifs <;> fun_prop

theorem F_Emb_perm {M k : ℕ} (hk : k ≤ M) (F : (Fin M → Fin k → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G)
    (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ) (hx : ∀ j, 0 < x j) :
    F (Emb M k (x ∘ σ)) = F (Emb M k x) := by
  refine F_emb hk F hL hR (Emb M k (x ∘ σ)) (perm_mem_unitary σ) x hx ?_
  rw [gram_Emb hk (x ∘ σ) (fun j => (hx (σ j)).le)]
  exact perm_conj_diag σ (fun i => (x i : ℂ))

abbrev Ppos (k : ℕ) : Set (Fin k → ℝ) := Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ))

theorem mem_Ppos {k : ℕ} {x : Fin k → ℝ} : x ∈ Ppos k ↔ ∀ j, 0 < x j := by simp [Ppos]

theorem Ppos_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ) : x ∘ σ ∈ Ppos k ↔ x ∈ Ppos k := by
  simp only [mem_Ppos, Function.comp_apply]
  exact ⟨fun hx j => by simpa using hx (σ.symm j), fun hx j => hx (σ j)⟩

/-- Symmetrisation over the positive orthant for a bi-invariant `H`. -/
theorem lintegral_Ppos_sym {M k : ℕ} (hk : k ≤ M) (H : (Fin M → Fin k → ℂ) → ENNReal) (hHm : Measurable H)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, H (Q * G) = H G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, H (G * V) = H G) (b : ℕ) :
    ∫⁻ x in Set.pi univ (fun _ : Fin k => Ioi (0 : ℝ)), H (Emb M k x) * ENNReal.ofReal (lag b x) =
      (k.factorial : ENNReal) * ∫⁻ x in SA k,
        (Ppos k).indicator (fun x => H (Emb M k x) * ENNReal.ofReal (lag b x)) x := by
  rw [← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)]
  refine lintegral_sym _ ?_ ?_
  · exact ((hHm.comp (continuous_Emb M k).measurable).mul
      (lag_continuous k b).measurable.ennreal_ofReal).indicator
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)
  · intro σ x
    by_cases hx : x ∈ Ppos k
    · rw [Set.indicator_of_mem ((Ppos_perm σ x).mpr hx), Set.indicator_of_mem hx, lag_perm,
        F_Emb_perm hk H hL hR σ x (mem_Ppos.mp hx)]
    · rw [Set.indicator_of_notMem (fun h => hx ((Ppos_perm σ x).mp h)), Set.indicator_of_notMem hx]

theorem lag_const {n : ℕ} (a b : ℕ) (hb : b = a + 1) {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i)
    (hv : 0 < vdm μ) :
    (∏ i, μ i)⁻¹ ^ b * Real.exp (∑ i, μ i) / vdm μ / (a.factorial : ℝ) * lag b μ =
      1 / (a.factorial : ℝ) * vdm μ := by
  subst hb
  have hP : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hμ i
  rw [lag_eq_vdm]
  have he : Real.exp (∑ i, μ i) * Real.exp (-∑ i, μ i) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hpp : (∏ i, μ i)⁻¹ ^ (a + 1) * (∏ i, μ i) ^ (a + 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hP.ne', one_pow]
  have hvv : vdm μ ^ 2 / vdm μ = vdm μ := by
    rw [sq, mul_div_assoc, div_self hv.ne', mul_one]
  calc (∏ i, μ i)⁻¹ ^ (a + 1) * Real.exp (∑ i, μ i) / vdm μ / (a.factorial : ℝ) *
        (vdm μ ^ 2 * (Real.exp (-∑ j, μ j) * (∏ j, μ j) ^ (a + 1)))
      = ((∏ i, μ i)⁻¹ ^ (a + 1) * (∏ i, μ i) ^ (a + 1)) *
          (Real.exp (∑ i, μ i) * Real.exp (-∑ i, μ i)) * (vdm μ ^ 2 / vdm μ) / (a.factorial : ℝ) := by ring
    _ = 1 / (a.factorial : ℝ) * vdm μ := by rw [hpp, he, hvv]; ring

noncomputable def Phi2 {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (a : ℕ)
    (la : Fin (n + 1) → ℝ) : ENNReal :=
  ENNReal.ofReal (vdm la) * F (Emb M (n + 1) la) * ENNReal.ofReal (wt a la)

theorem measurable_Phi2 {M n : ℕ} {F : (Fin M → Fin (n + 1) → ℂ) → ENNReal} (hFm : Measurable F) (a : ℕ) :
    Measurable (Phi2 F a) := by
  have hwtm : Measurable (fun la : Fin (n + 1) → ℝ => wt a la) := by
    unfold wt
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply _))
      (by fun_prop : Continuous fun la : Fin (n + 1) → ℝ =>
        Real.exp (-∑ j, la j) * (∏ j, la j) ^ a).measurable measurable_const
  exact (continuous_vdm.measurable.ennreal_ofReal.mul
    (hFm.comp (continuous_Emb M (n + 1)).measurable)).mul hwtm.ennreal_ofReal

/-- One induction step of the array Weyl formula. -/
theorem lagWeyl2_step {M n : ℕ} (h : n + 1 ≤ M) (H : LagWeyl2 n M) : LagWeyl2 (n + 1) M := by
  classical
  obtain ⟨c, hc⟩ := H
  have hMa : M - n = M - n - 1 + 1 := by omega
  have hMa' : M - (n + 1) = M - n - 1 := by omega
  refine ⟨c * ((n.factorial : ENNReal) * (ENNReal.ofReal (1 / ((M - n - 1).factorial : ℝ)) *
    (ENNReal.ofReal (1 / (n.factorial : ℝ)) * ((n + 1).factorial : ENNReal)⁻¹))),
    fun F hFm hL hR => ?_⟩
  have hWm := measurable_hW F hFm
  have hWL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin n) ℂ, hW F (Q * G) = hW F G :=
    fun Q hQ G => hW_left F hFm hL hQ G
  have hWR : ∀ V ∈ unitaryGroup (Fin n) ℂ, ∀ G : Matrix (Fin M) (Fin n) ℂ, hW F (G * V) = hW F G :=
    fun V hV G => hW_right F hR hV G
  have hΦm : Measurable (Phi2 F (M - n - 1)) := measurable_Phi2 hFm _
  set T : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ENNReal := fun p =>
    if p.2 ∈ Ilace p.1 then ENNReal.ofReal (vdm p.1) * Phi2 F (M - n - 1) p.2 else 0 with hT
  have hTm : Measurable T :=
    Measurable.ite (measurableSet_E n)
      ((continuous_vdm.measurable.ennreal_ofReal.comp measurable_fst).mul (hΦm.comp measurable_snd))
      measurable_const
  -- (a) the chamber integrand
  have hA : ∫⁻ μ in SA n, (Ppos n).indicator
        (fun μ => hW F (Emb M n μ) * ENNReal.ofReal (lag (M - n) μ)) μ =
      ENNReal.ofReal (1 / ((M - n - 1).factorial : ℝ)) * ∫⁻ μ, ∫⁻ la, T (μ, la) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (measurableSet_SA n)]
    refine lintegral_congr fun μ => ?_
    by_cases hμ : μ ∈ SA n
    · rw [Set.indicator_of_mem hμ]
      by_cases hp : μ ∈ Ppos n
      · rw [Set.indicator_of_mem hp]
        have hpos := mem_Ppos.mp hp
        have hv : 0 < vdm μ := vdm_pos (show StrictAnti μ from hμ).injective
        have hPμ : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hpos i
        have hd : hW F (Emb M n μ) = ENNReal.ofReal ((∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) /
            vdm μ / ((M - n - 1).factorial : ℝ)) * ∫⁻ la in Ilace μ, Phi2 F (M - n - 1) la :=
          hW_diag h F hFm hL hR hμ hpos
        have hin : ∫⁻ la, T (μ, la) =
            ENNReal.ofReal (vdm μ) * ∫⁻ la in Ilace μ, Phi2 F (M - n - 1) la := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_indicator (measurableSet_Ilace μ)]
          refine lintegral_congr fun la => ?_
          simp only [hT, Set.indicator_apply]
        have hK : 0 ≤ (∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ /
            ((M - n - 1).factorial : ℝ) :=
          div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hPμ).le _) (Real.exp_pos _).le)
            (vdm_nonneg μ)) (Nat.cast_nonneg _)
        rw [hd, hin]
        calc ENNReal.ofReal ((∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ /
              ((M - n - 1).factorial : ℝ)) * (∫⁻ la in Ilace μ, Phi2 F (M - n - 1) la) *
              ENNReal.ofReal (lag (M - n) μ)
            = ENNReal.ofReal ((∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ /
              ((M - n - 1).factorial : ℝ) * lag (M - n) μ) *
                ∫⁻ la in Ilace μ, Phi2 F (M - n - 1) la := by
              rw [ENNReal.ofReal_mul hK]; ring
          _ = ENNReal.ofReal (1 / ((M - n - 1).factorial : ℝ)) *
              (ENNReal.ofReal (vdm μ) * ∫⁻ la in Ilace μ, Phi2 F (M - n - 1) la) := by
              rw [lag_const (M - n - 1) (M - n) hMa hpos hv, ENNReal.ofReal_mul (by positivity),
                mul_assoc]
      · rw [Set.indicator_of_notMem hp]
        have hz : ∀ la, T (μ, la) = 0 := by
          intro la
          simp only [hT]
          split_ifs with hla
          · have hl : ¬ 0 < la (Fin.last n) := by
              intro hl
              refine hp (mem_Ppos.mpr fun i => ?_)
              exact lt_of_lt_of_le hl ((ilace_strictAnti hla).antitone (Fin.le_last _)) |>.trans
                (hla i).2
            simp [Phi2, wt, hl]
          · rfl
        simp [hz]
    · rw [Set.indicator_of_notMem hμ]
      have hz : ∀ la, T (μ, la) = 0 := by
        intro la
        simp only [hT]
        rw [if_neg]
        intro hla; exact hμ (ilace_mu_strictAnti hla)
      simp [hz]
  -- (b) swap and integrate over the box
  have hD : ∫⁻ la, ∫⁻ μ, T (μ, la) =
      ∫⁻ la in SA (n + 1), Phi2 F (M - n - 1) la * ENNReal.ofReal (vdm la / (n.factorial : ℝ)) := by
    rw [← lintegral_indicator (measurableSet_SA (n + 1))]
    refine lintegral_congr fun la => ?_
    have hbox : ∫⁻ μ, T (μ, la) = (∫⁻ μ in box la, ENNReal.ofReal (vdm μ)) * Phi2 F (M - n - 1) la := by
      rw [← lintegral_mul_const _ continuous_vdm.measurable.ennreal_ofReal,
        ← lintegral_indicator (measurableSet_box la)]
      refine lintegral_congr fun μ => ?_
      simp only [hT, Set.indicator_apply, mem_box_iff]
    rw [hbox]
    by_cases hla : la ∈ SA (n + 1)
    · rw [Set.indicator_of_mem hla, lintegral_box_vdm (show StrictAnti la from hla), mul_comm]
    · rw [Set.indicator_of_notMem hla]
      have he : box la = ∅ := by
        ext μ
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hμ
        exact hla (ilace_strictAnti (mem_box_iff.mp hμ))
      simp [he]
  -- (c) back to the Laguerre weight
  have hE : ∫⁻ la in SA (n + 1), Phi2 F (M - n - 1) la * ENNReal.ofReal (vdm la / (n.factorial : ℝ)) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) * ∫⁻ la in SA (n + 1), (Ppos (n + 1)).indicator
        (fun x => F (Emb M (n + 1) x) * ENNReal.ofReal (lag (M - n - 1) x)) la := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_SA _) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hpos : ∀ j, 0 < la j := fun j =>
        lt_of_lt_of_le hl ((show StrictAnti la from hla).antitone (Fin.le_last j))
      rw [Set.indicator_of_mem (mem_Ppos.mpr hpos)]
      have hwt : wt (M - n - 1) la = Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1) := by
        rw [wt, if_pos hl]
      simp only [Phi2]
      rw [hwt, lag_eq_vdm, div_eq_mul_one_div (vdm la), ENNReal.ofReal_mul (vdm_nonneg la),
        ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (vdm_nonneg la)]
      ring
    · rw [Set.indicator_of_notMem (fun hp => hl (mem_Ppos.mp hp _))]
      simp [Phi2, wt, hl]
  -- (d) unsymmetrise
  have hF2 : ∫⁻ la in SA (n + 1), (Ppos (n + 1)).indicator
        (fun x => F (Emb M (n + 1) x) * ENNReal.ofReal (lag (M - n - 1) x)) la =
      ((n + 1).factorial : ENNReal)⁻¹ * ∫⁻ x in Set.pi univ (fun _ : Fin (n + 1) => Ioi (0 : ℝ)),
        F (Emb M (n + 1) x) * ENNReal.ofReal (lag (M - n - 1) x) := by
    rw [lintegral_Ppos_sym h F hFm hL hR (M - n - 1), ← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos _).ne') (ENNReal.natCast_ne_top _),
      one_mul]
  rw [hMa', step_eq2 F hFm, hc (hW F) hWm hWL hWR, lintegral_Ppos_sym (by omega) (hW F) hWm hWL hWR (M - n),
    hA, lintegral_lintegral_swap (f := fun μ la => T (μ, la)) hTm.aemeasurable, hD, hE, hF2]
  ring

theorem lagWeyl2_zero (M : ℕ) : LagWeyl2 0 M := by
  refine ⟨1, fun F _ _ _ => ?_⟩
  have hs : Set.pi univ (fun _ : Fin 0 => Ioi (0 : ℝ)) = univ :=
    Set.eq_univ_of_forall fun x => Set.mem_univ_pi.mpr fun i => i.elim0
  have h1 : ∀ G : Fin M → Fin 0 → ℂ, F G = F 0 := fun G => congrArg F (Subsingleton.elim _ _)
  have h2 : ∀ x : Fin 0 → ℝ, F (Emb M 0 x) * ENNReal.ofReal (lag (M - 0) x) = F 0 := by
    intro x
    rw [Subsingleton.elim (α := Fin M → Fin 0 → ℂ) (Emb M 0 x) 0]
    simp [lag, vandSq]
  simp only [h1, h2, hs, Measure.restrict_univ, lintegral_const, measure_univ, one_mul, mul_one]
  rw [volume_pi, Measure.pi_of_empty]
  simp

theorem lagWeyl2_all (M : ℕ) : ∀ k, k ≤ M → LagWeyl2 k M := by
  intro k
  induction k with
  | zero => intro _; exact lagWeyl2_zero M
  | succ n ih => intro hk; exact lagWeyl2_step hk (ih (by omega))

end SWL302

open SpikedWishart.FixedDim MeasureTheory Set in
theorem solution (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (π₁ : ℝ) (hπ₁ : 0 < π₁) (t : ℝ) :
    (sampleLaw M k).real {Y | SpikedWishart.Separated.largestEig M 1 (fun _ => π₁⁻¹) Y ≤ t} =
      (C M k π₁)⁻¹ * ∫ y in Set.pi univ (fun _ : Fin k => Ioc 0 t), w M π₁ y := by
  exact SWL302.eq302_of_lag k M hk hkM π₁ hπ₁ t
    (SWL302.lagWeyl_of_two k M hkM (SWL302.lagWeyl2_all M k hkM))

