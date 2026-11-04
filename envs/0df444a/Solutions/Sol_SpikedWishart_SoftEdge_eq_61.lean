-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_61
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:46:31.539386+00:00
-- url     : https://prove2.me/submissions/58626078-0d26-4d65-b982-1b8632b3bb41

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_Model
import Definitions.Def_SpikedWishart_LastPassage_LPP
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre
import Definitions.Def_SpikedWishart_SoftEdge_Model
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option linter.all false

set_option maxHeartbeats 2000000

set_option autoImplicit false

-- ===== G0: b8c3944b Weyl + SWL302 prefix (c2c, chain_tele)
section G0Sec



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

end Weyl

end

-- ===== from W4a.lean =====
section

namespace Weyl

open Finset

/-- The box `Π_i (λ_{i+1}, λ_i)` of the `μ` interlacing `λ`. -/
def box {n : ℕ} (la : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i : Fin n => Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))

theorem vdm_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ vdm v :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- The sign `∏_{i<j} (-1)`. -/
noncomputable def sgn (m : ℕ) : ℝ := ∏ i : Fin m, ∏ _j ∈ Ioi i, (-1 : ℝ)

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

theorem continuous_vdm {m : ℕ} : Continuous (fun v : Fin m → ℝ => vdm v) := by
  unfold vdm; fun_prop

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

/-! ## Array form of the Weyl formula (A2) and its consequence `LagWeyl` -/

/-- The `M × k` matrix with `√x_j` at `(j, j)` and zeros elsewhere. -/
noncomputable def Emb (M k : ℕ) (x : Fin k → ℝ) : Matrix (Fin M) (Fin k) ℂ :=
  fun m j => if (m : ℕ) = j then ((Real.sqrt (x j) : ℝ) : ℂ) else 0

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

end SWL302

/-! C2a (b8c3944b): nonnull (column-weighted) Laguerre chain formula, built on the d80e94b4 lib
(prefix 53ec8574_w6b + S0..S7). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- squared Frobenius norm. -/
noncomputable def frob {M k : ℕ} (G : Fin M → Fin k → ℂ) : ℝ := ∑ m, ∑ j, Complex.normSq (G m j)

theorem continuous_frob (M k : ℕ) : Continuous (fun G : Fin M → Fin k → ℂ => frob G) := by
  unfold frob; fun_prop

theorem frob_eq_trace {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) : ((frob G : ℝ) : ℂ) = (Gᴴ * G).trace := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem frob_left {M k : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : frob (Q * G) = frob G := by
  apply Complex.ofReal_injective
  rw [frob_eq_trace, frob_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
    show Qᴴ * Q = 1 from (mem_unitaryGroup_iff'.mp hQ), Matrix.one_mul]

theorem frob_right {M k : ℕ} {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : frob (G * V) = frob G := by
  apply Complex.ofReal_injective
  rw [frob_eq_trace, frob_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc G, show V * Vᴴ = 1 from (mem_unitaryGroup_iff.mp hV), Matrix.mul_one]

theorem frob_Emb {M k : ℕ} (hk : k ≤ M) {x : Fin k → ℝ} (hx : ∀ j, 0 ≤ x j) :
    frob (Emb M k x) = ∑ j, x j := by
  unfold frob
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin M)]
  · simp only [Emb, ↓reduceIte, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (hx j)
  · intro m _ hm
    have : (m : ℕ) ≠ j := fun h => hm (Fin.ext h)
    simp [Emb, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem frob_join {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) :
    frob (join G' g) = frob G' + ∑ m, Complex.normSq (g m) := by
  unfold frob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_castSucc]
  simp only [join, Fin.snoc_castSucc, Fin.snoc_last]

/-- column weights `∏_j exp(-a_j |col_j|²)`. -/
noncomputable def colW {M k : ℕ} (a : ℕ → ℝ) (G : Fin M → Fin k → ℂ) : ENNReal :=
  ∏ j : Fin k, ENNReal.ofReal (Real.exp (-(a j) * ∑ m, Complex.normSq (G m j)))

theorem measurable_colW {M k : ℕ} (a : ℕ → ℝ) : Measurable (fun G : Fin M → Fin k → ℂ => colW a G) := by
  unfold colW
  refine Finset.measurable_prod _ fun j _ => ?_
  exact (by fun_prop : Continuous fun G : Fin M → Fin k → ℂ =>
    Real.exp (-(a j) * ∑ m, Complex.normSq (G m j))).measurable.ennreal_ofReal

theorem colW_join {M n : ℕ} (a : ℕ → ℝ) (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) :
    colW a (join G' g) = colW (fun j => a j - a n) G' * ENNReal.ofReal (Real.exp (-(a n) * frob (join G' g))) := by
  have hcol : ∀ j : Fin n, (∑ m, Complex.normSq (join G' g m (Fin.castSucc j))) = ∑ m, Complex.normSq (G' m j) := by
    intro j; simp only [join, Fin.snoc_castSucc]
  have hlast : (∑ m, Complex.normSq (join G' g m (Fin.last n))) = ∑ m, Complex.normSq (g m) := by
    simp only [join, Fin.snoc_last]
  unfold colW
  rw [Fin.prod_univ_castSucc]
  simp only [hcol, hlast, Fin.val_last, Fin.val_castSucc]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
  congr 1
  rw [frob_join, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hf : frob G' = ∑ j : Fin n, ∑ m, Complex.normSq (G' m j) := by unfold frob; exact Finset.sum_comm
  have hs : ∑ j : Fin n, -(a j - a n) * ∑ m, Complex.normSq (G' m j) =
      ∑ j : Fin n, -(a j) * ∑ m, Complex.normSq (G' m j) + a n * ∑ j : Fin n, ∑ m, Complex.normSq (G' m j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hf, hs]
  ring

/-- normalising factor of the bordering kernel. -/
noncomputable def kc (M n : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ / ((M - n - 1).factorial : ℝ)

/-- the weighted interlacing chain integral (level `k`, innermost = top level). -/
noncomputable def chain (M : ℕ) (a : ℕ → ℝ) : (k : ℕ) → ((Fin k → ℝ) → ENNReal) → ENNReal
  | 0, Ψ => Ψ (fun i => i.elim0)
  | n + 1, Ψ => chain M a n (fun μ => ENNReal.ofReal (kc M n μ) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))))

theorem chain_succ (M : ℕ) (a : ℕ → ℝ) (n : ℕ) (Ψ : (Fin (n + 1) → ℝ) → ENNReal) :
    chain M a (n + 1) Ψ = chain M a n (fun μ => ENNReal.ofReal (kc M n μ) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)))) := rfl

/-- good set: strictly decreasing and positive. -/
def Good (k : ℕ) : Set (Fin k → ℝ) := {μ | StrictAnti μ ∧ ∀ i, 0 < μ i}

theorem chain_congr_good (M : ℕ) (a : ℕ → ℝ) (k : ℕ) (Ψ Ψ' : (Fin k → ℝ) → ENNReal)
    (h : ∀ μ ∈ Good k, Ψ μ = Ψ' μ) : chain M a k Ψ = chain M a k Ψ' := by
  cases k with
  | zero =>
    show Ψ _ = Ψ' _
    exact h _ ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    rw [chain_succ, chain_succ]
    congr 1
    funext μ
    congr 1
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      rw [h la ⟨hsa, fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))⟩]
    · simp [wt, hl]

theorem chain_shift (M : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    ∀ (k : ℕ) (Ψ : (Fin k → ℝ) → ENNReal),
      chain M (fun j => a j - c) k (fun μ => ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) * Ψ μ) = chain M a k Ψ := by
  intro k
  induction k with
  | zero => intro Ψ; show ENNReal.ofReal _ * Ψ _ = Ψ _; simp
  | succ n ih =>
    intro Ψ
    rw [chain_succ, chain_succ, ← ih]
    congr 1
    funext μ
    rw [mul_left_comm (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))),
      ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))) _ ENNReal.ofReal_ne_top]
    congr 1
    refine lintegral_congr fun la => ?_
    have e : ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) *
        ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i))) =
        ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    calc ENNReal.ofReal (vdm la) * (ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) * Ψ la) *
          ENNReal.ofReal (wt (M - n - 1) la) * ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i)))
        = ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
          (ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) *
            ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i)))) := by ring
      _ = _ := by rw [e]; ring

end SWL302

-- ===== from C2b.lean =====

/-! C2b (b8c3944b): induction for the column-weighted Laguerre chain formula. Needs C2a. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- weighted array Weyl formula at level `k`, as an interlacing chain integral. -/
def NW (k M : ℕ) : Prop :=
  ∀ a : ℕ → ℝ, ∀ F : (Fin M → Fin k → ℂ) → ENNReal, Measurable F →
    (∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G) →
    (∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G) →
    ∫⁻ G, F G * colW a G ∂(sampleLaw M k) = chain M a k (fun la => F (Emb M k la))

theorem nw_zero (M : ℕ) : NW 0 M := by
  intro a F _ _ _
  have h1 : ∀ G : Fin M → Fin 0 → ℂ, F G * colW a G = F 0 := fun G => by
    rw [Subsingleton.elim G 0]; simp [colW]
  simp only [h1, lintegral_const, measure_univ, mul_one]
  show F 0 = F (Emb M 0 _)
  rw [Subsingleton.elim (α := Fin M → Fin 0 → ℂ) (Emb M 0 _) 0]

theorem nw_step {M n : ℕ} (h : n + 1 ≤ M) (H : NW n M) : NW (n + 1) M := by
  intro a F hFm hL hR
  set c := a n with hc
  set F' : (Fin M → Fin (n + 1) → ℂ) → ENNReal := fun G => F G * ENNReal.ofReal (Real.exp (-c * frob G))
    with hF'def
  have hF'm : Measurable F' :=
    hFm.mul (Real.measurable_exp.comp ((continuous_frob M (n + 1)).measurable.const_mul (-c))).ennreal_ofReal
  have hF'L : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F' (Q * G) = F' G := by
    intro Q hQ G
    show F (Q * G) * _ = F G * _
    rw [hL Q hQ G, frob_left hQ G]
  have hF'R : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F' (G * V) = F' G := by
    intro V hV G
    show F (G * V) * _ = F G * _
    rw [hR V hV G, frob_right hV G]
  have hprod : Measurable fun G : Fin M → Fin (n + 1) → ℂ => F G * colW a G := hFm.mul (measurable_colW a)
  have hpt : ∀ G' : Fin M → Fin n → ℂ, hW (fun G => F G * colW a G) G' =
      hW F' G' * colW (fun j => a j - c) G' := by
    intro G'
    unfold hW
    rw [← lintegral_mul_const' (colW (fun j => a j - c) G') _
      (by unfold colW; exact ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun g => ?_
    show F (join G' g) * colW a (join G' g) = _
    rw [colW_join, ← hc]
    simp only [hF'def]
    ring
  rw [step_eq2 _ hprod, lintegral_congr hpt,
    H (fun j => a j - c) (hW F') (measurable_hW F' hF'm) (fun Q hQ G => hW_left F' hF'm hF'L hQ G)
      (fun V hV G => hW_right F' hF'R hV G),
    chain_succ, ← chain_shift M a c n]
  apply chain_congr_good
  rintro μ ⟨hanti, hpos⟩
  rw [hW_diag h F' hF'm hF'L hF'R hanti hpos, mul_left_comm (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))),
    ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))) _ ENNReal.ofReal_ne_top]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
  by_cases hl : 0 < la (Fin.last n)
  · have hsa := ilace_strictAnti hla
    have hlp : ∀ j, 0 ≤ la j := fun j => (lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))).le
    simp only [hF'def]
    rw [frob_Emb h hlp]
    have e : ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) =
        ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) * ENNReal.ofReal (Real.exp (-c * (∑ j, la j - ∑ i, μ i))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    rw [e]
    ring
  · simp [wt, hl]

theorem nw_all (M : ℕ) : ∀ k, k ≤ M → NW k M := by
  intro k
  induction k with
  | zero => intro _; exact nw_zero M
  | succ n ih => intro hk; exact nw_step hk (ih (by omega))

end SWL302

-- ===== from C2f.lean =====

/-! C2f (b8c3944b): column scaling of the Gaussian array is absolutely continuous with an explicit
density (complex Gaussian of variance c⁻¹ vs variance 1). Standalone (Mathlib + FixedDim model). -/


namespace SWL302

open MeasureTheory ProbabilityTheory SpikedWishart.FixedDim

theorem lintegral_pi_prod_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (g : ι → α → ENNReal) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : ι → α, ∏ i, g i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, g i t ∂μ := by
  have hF : Measurable fun x : ι → α => ∏ i, g i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  have key : ∀ s : Finset ι, ∀ x : ι → α,
      (∫⋯∫⁻_s, (fun x : ι → α => ∏ i, g i (x i)) ∂(fun _ => μ)) x =
        ∏ i, (if i ∈ s then ∫⁻ t, g i t ∂μ else g i (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp [lmarginal_empty]
    | @insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hF hi]
      simp_rw [ih]
      have h1 : ∀ t : α, (∏ k, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (Function.update x i t k))) =
          g i t * ∏ k ∈ Finset.univ.erase i, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (x k)) := by
        intro t
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [if_neg hi, Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp_rw [h1]
      rw [lintegral_mul_const _ (hg i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Finset.mem_insert, true_or, if_true]
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [Finset.ne_of_mem_erase hk]
  rw [lintegral_eq_lmarginal_univ (fun _ => (default : α)), key]
  simp

theorem pi_withDensity_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (f : ι → α → ENNReal)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi fun _ => μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ι → α, (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod_gen μ _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

theorem gR_scale_aux (c : ℝ) (hc : 0 < c) (v : NNReal) (hv : (v : ℝ) = c⁻¹ * (1 / 2)) :
    gaussianReal 0 v =
      (gaussianReal 0 (1 / 2 : NNReal)).withDensity
        (fun t => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv
    have : (0 : ℝ) < c⁻¹ * (1 / 2) := mul_pos (inv_pos.mpr hc) (by norm_num)
    linarith
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
    fun_prop
  rw [gaussianReal_of_var_ne_zero _ hv0,
    gaussianReal_of_var_ne_zero _ (by norm_num : (1 / 2 : NNReal) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hr]
  congr 1
  funext t
  simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hv]
  have h12 : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [h12]
  have hpi := Real.pi_pos
  have hs1 : Real.sqrt (2 * Real.pi * (c⁻¹ * (1 / 2))) = Real.sqrt Real.pi / Real.sqrt c := by
    rw [show 2 * Real.pi * (c⁻¹ * (1 / 2)) = Real.pi / c by field_simp, Real.sqrt_div hpi.le]
  have hs2 : Real.sqrt (2 * Real.pi * (1 / 2)) = Real.sqrt Real.pi := by
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  rw [hs1, hs2]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have he : Real.exp (-(t - 0) ^ 2 / (2 * (c⁻¹ * (1 / 2)))) =
      Real.exp (-(t - 0) ^ 2 / (2 * (1 / 2))) * Real.exp (-(c - 1) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [he, inv_div]
  field_simp

/-- real Gaussian of variance `1/(2c)` against variance `1/2`. -/
theorem gR_scale (c : ℝ) (hc : 0 < c) :
    (gaussianReal 0 (1 / 2 : NNReal)).map (fun t => Real.sqrt c⁻¹ * t) =
      (gaussianReal 0 (1 / 2 : NNReal)).withDensity
        (fun t => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  refine gR_scale_aux c hc _ ?_
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.sq_sqrt (inv_nonneg.mpr hc.le)]
  norm_num

/-- complex Gaussian of variance `1/c` against the standard one. -/
theorem cg_scale (c : ℝ) (hc : 0 < c) :
    stdComplexGaussian.map (fun z => ((Real.sqrt c⁻¹ : ℝ) : ℂ) * z) =
      stdComplexGaussian.withDensity
        (fun z => ENNReal.ofReal (c * Real.exp (-(c - 1) * Complex.normSq z))) := by
  set s := Real.sqrt c⁻¹ with hs
  have hC : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
    fun_prop
  have hm : Measurable (fun t : ℝ => s * t) := measurable_const_mul s
  unfold stdComplexGaussian
  rw [Measure.map_map (by fun_prop) hC]
  have e1 : (fun z : ℂ => ((s : ℝ) : ℂ) * z) ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) ∘ Prod.map (fun t => s * t) (fun t => s * t) := by
    funext p
    apply Complex.ext <;> simp
  rw [e1, ← Measure.map_map hC (hm.prodMap hm),
    ← Measure.map_prod_map _ _ hm hm, gR_scale c hc, prod_withDensity hr hr]
  ext t ht
  rw [Measure.map_apply hC ht, withDensity_apply _ ht, withDensity_apply _ (hC ht),
    Measure.restrict_map hC ht, lintegral_map (by fun_prop) hC]
  refine setLIntegral_congr_fun (hC ht) (fun p _ => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Complex.normSq_mk]
  rw [mul_mul_mul_comm, ← Real.exp_add, Real.mul_self_sqrt hc.le]
  congr 2
  ring

/-- the density of the column-scaled array against the standard array. -/
noncomputable def sclW {M N : ℕ} (c : Fin N → ℝ) (G : Fin M → Fin N → ℂ) : ENNReal :=
  ∏ m, ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (G m j)))

theorem measurable_sclW {M N : ℕ} (c : Fin N → ℝ) :
    Measurable (fun G : Fin M → Fin N → ℂ => sclW c G) := by
  unfold sclW
  refine Finset.measurable_prod _ fun m _ => Finset.measurable_prod _ fun j _ => ?_
  have h : Measurable (fun G : Fin M → Fin N → ℂ => G m j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply m)
  exact (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (Complex.continuous_normSq.measurable.comp h)))).ennreal_ofReal

theorem sample_scale {M N : ℕ} (c : Fin N → ℝ) (hc : ∀ j, 0 < c j) :
    (sampleLaw M N).map (fun G m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) =
      (sampleLaw M N).withDensity (sclW c) := by
  have hw : ∀ j, Measurable
      (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) := fun j =>
    (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul Complex.continuous_normSq.measurable))).ennreal_ofReal
  have hcs : ∀ j, stdComplexGaussian.map (fun z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z) =
      stdComplexGaussian.withDensity
        (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) :=
    fun j => cg_scale (c j) (hc j)
  have hP : ∀ j, IsProbabilityMeasure (stdComplexGaussian.withDensity
      (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z)))) := fun j => by
    rw [← hcs j]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hh : Measurable (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j) := by
    fun_prop
  have h1 := Measure.pi_map_pi (μ := fun _ : Fin N => stdComplexGaussian)
    (f := fun j z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z) (fun j => (by fun_prop : Measurable _).aemeasurable)
  have hinner : (Measure.pi fun _ : Fin N => stdComplexGaussian).map
      (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j) =
      (Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
        (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) := by
    refine h1.trans ?_
    have e : (fun j => stdComplexGaussian.map (fun z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z)) =
        fun j => stdComplexGaussian.withDensity
          (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) := funext hcs
    rw [e]
    exact @pi_withDensity_gen (Fin N) ℂ _ _ _ _ stdComplexGaussian _ _ hw (fun j => by haveI := hP j; infer_instance)
  have hW : Measurable (fun g : Fin N → ℂ =>
      ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) :=
    Finset.measurable_prod _ fun j _ => (hw j).comp (measurable_pi_apply j)
  have hP2 : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
      (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j))))) := by
    rw [← hinner]; exact Measure.isProbabilityMeasure_map hh.aemeasurable
  have h2 := Measure.pi_map_pi (μ := fun _ : Fin M => Measure.pi fun _ : Fin N => stdComplexGaussian)
    (f := fun _ (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j)
    (fun _ => hh.aemeasurable)
  have hs : sclW (M := M) c = fun G => ∏ m, (fun g : Fin N → ℂ =>
      ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) (G m) := by
    funext G; rfl
  unfold sampleLaw
  refine h2.trans ?_
  rw [hs]
  have e2 : (fun _ : Fin M => (Measure.pi fun _ : Fin N => stdComplexGaussian).map
      (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j)) =
      fun _ : Fin M => (Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
        (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) :=
    funext fun _ => hinner
  rw [e2]
  exact @pi_withDensity_gen (Fin M) (Fin N → ℂ) _ _ _ _ _ _ _ (fun _ => hW) (fun _ => by haveI := hP2; infer_instance)

theorem lintegral_scale {M N : ℕ} (c : Fin N → ℝ) (hc : ∀ j, 0 < c j)
    (F : (Fin M → Fin N → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ G, F (fun m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) ∂(sampleLaw M N) =
      ∫⁻ G, sclW c G * F G ∂(sampleLaw M N) := by
  have hs : Measurable (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) := by
    fun_prop
  rw [← lintegral_map hF hs, sample_scale c hc,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_sclW c) hF]
  rfl

end SWL302

-- ===== from C2c.lean =====

/-! C2c (b8c3944b): the spiked largest-eigenvalue CDF as a weighted interlacing chain integral.
Needs C2a, C2b, C2f and the d80e94b4 lib (isClosed_psdSet, psd_conj_iff, ind_psd_conj, ind_diag, Wm_*). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- spike weights `π_j - 1` as a sequence. -/
noncomputable def aπ {N : ℕ} (π : Fin N → ℝ) : ℕ → ℝ := fun j => if h : j < N then π ⟨j, h⟩ - 1 else 0

theorem aπ_fin {N : ℕ} (π : Fin N → ℝ) (j : Fin N) : aπ π j = π j - 1 := by
  simp [aπ, j.isLt]

theorem Wm_eq_sum {M k : ℕ} (X : Fin M → Fin k → ℂ) :
    Wm X = ∑ m, vecMulVec (X m) (star (X m)) := by
  ext i j
  rw [Matrix.sum_apply]
  rfl

theorem sampleCov_scale {M N : ℕ} (U : unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) :
    SpikedWishart.SoftEdge.sampleCov M U ℓ G =
      (M : ℂ)⁻¹ • ((U : Matrix (Fin N) (Fin N) ℂ) *
        Wm (fun m j => ((Real.sqrt (ℓ j) : ℝ) : ℂ) * G m j) * star (U : Matrix (Fin N) (Fin N) ℂ)) := by
  unfold SpikedWishart.SoftEdge.sampleCov SpikedWishart.SoftEdge.sampleVec
  congr 1
  rw [Wm_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, star_eq_conjTranspose]

theorem event_scale {M N : ℕ} [NeZero N] (hM : 0 < M) (U : unitaryGroup (Fin N) ℂ) (π : Fin N → ℝ)
    (x : ℝ) (G : Fin M → Fin N → ℂ) :
    SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x ↔
      ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        Wm (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j)).PosSemidef := by
  unfold SpikedWishart.SoftEdge.largestEig
  rw [ciSup_le_iff (Set.finite_range _).bddAbove, SWL302Eig.eig_le_iff_posSemidef, sampleCov_scale]
  set W := Wm (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j)
  set V : Matrix (Fin N) (Fin N) ℂ := (U : Matrix (Fin N) (Fin N) ℂ)
  rw [← psd_conj_iff ((M : ℝ) * x) U.2 W]
  have hβ : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hb : ((M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have key : (((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - V * W * star V =
      ((M : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (M : ℂ)⁻¹ • (V * W * star V)) := by
    rw [smul_sub, smul_smul, smul_smul, show ((M : ℝ) : ℂ) = (M : ℂ) by push_cast; rfl,
      mul_inv_cancel₀ (by exact_mod_cast hβ.ne' : (M : ℂ) ≠ 0), one_smul]
    push_cast
    rfl
  rw [key]
  constructor
  · intro h
    exact h.smul (Complex.zero_le_real.mpr hβ.le)
  · intro h
    have h2 := h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hβ.le))
    rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hβ.ne', Complex.ofReal_one, one_smul] at h2

theorem sclW_eq {M N : ℕ} (π : Fin N → ℝ) (hπ : ∀ j, 0 < π j) (G : Fin M → Fin N → ℂ) :
    sclW π G = (∏ j, ENNReal.ofReal (π j ^ M)) * colW (aπ π) G := by
  unfold sclW colW
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [aπ_fin, ← ENNReal.ofReal_prod_of_nonneg (fun m _ => (mul_pos (hπ j) (Real.exp_pos _)).le),
    ← ENNReal.ofReal_mul (pow_nonneg (hπ j).le M)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    Finset.mul_sum]

theorem c2c {M N : ℕ} [NeZero N] (hNM : N ≤ M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i)
    (U : unitaryGroup (Fin N) ℂ) (x : ℝ) :
    (sampleLaw M N) {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} =
      (∏ i, ENNReal.ofReal (π i ^ M)) *
        chain M (aπ π) N (fun la => if la 0 ≤ (M : ℝ) * x then 1 else 0) := by
  have hM : 0 < M := lt_of_lt_of_le (NeZero.pos N) hNM
  set F : (Fin M → Fin N → ℂ) → ENNReal := fun G =>
    {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}.indicator
      (1 : Matrix (Fin N) (Fin N) ℂ → ENNReal) (Wm G) with hFdef
  have hT : MeasurableSet ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
      {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}) :=
    ((isClosed_psdSet ((M : ℝ) * x)).preimage (continuous_Wm M N)).measurableSet
  have hFe : F = ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
      {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}).indicator 1 := by
    funext G
    first | rfl | simp [hFdef, Set.indicator]
  have hF : Measurable F := by rw [hFe]; exact measurable_one.indicator hT
  have hs : Measurable (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
    fun_prop
  have hev : {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} =
      (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) ⁻¹'
        ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
          {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}) := by
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact event_scale hM U π x G
  rw [hev, ← lintegral_indicator_one (hs hT)]
  have h1 : ∀ G : Fin M → Fin N → ℂ,
      ((fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) ⁻¹'
        ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
          {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef})).indicator 1 G =
        F (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
    intro G
    rw [hFe]
    first | rfl | simp [Set.indicator]
  rw [lintegral_congr h1, lintegral_scale π hπ F hF]
  simp_rw [sclW_eq π hπ]
  have h2 : ∀ G : Fin M → Fin N → ℂ, (∏ j, ENNReal.ofReal (π j ^ M)) * colW (aπ π) G * F G =
      (∏ j, ENNReal.ofReal (π j ^ M)) * (F G * colW (aπ π) G) := fun G => by ring
  rw [lintegral_congr h2, lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top)]
  congr 1
  rw [nw_all M N hNM (aπ π) F hF
    (fun Q hQ G => by simp only [hFdef]; rw [Wm_mul_left hQ G])
    (fun V hV G => by
      simp only [hFdef]
      rw [Wm_mul_right G V]
      exact ind_psd_conj ((M : ℝ) * x) (transpose_mem_unitary hV) (Wm G))]
  apply chain_congr_good
  rintro la ⟨hanti, hpos⟩
  simp only [hFdef]
  rw [Wm_Emb hNM la (fun j => (hpos j).le), ind_diag]
  by_cases h0 : la 0 ≤ (M : ℝ) * x
  · rw [if_pos h0, Set.indicator_of_mem]
    · rfl
    · intro j _
      exact le_trans (hanti.antitone (Fin.zero_le j)) h0
  · rw [if_neg h0, Set.indicator_of_notMem]
    intro hm
    exact h0 (hm 0 (Set.mem_univ _))

end SWL302

-- ===== from C2g.lean =====

/-! C2g (b8c3944b): telescoping the weighted chain into a plain Gelfand-Tsetlin nested integral
with level weights e^{-b_n(|la|-|μ|)} and top density vdm la (∏ la)^(M-k) / ∏_{n<k} (M-n-1)!. Needs C2a. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- positivity indicator of the last coordinate. -/
noncomputable def posI {n : ℕ} (la : Fin (n + 1) → ℝ) : ℝ := if 0 < la (Fin.last n) then 1 else 0

/-- nested Gelfand-Tsetlin integral with level weights `e^{-b_n(|la|-|μ|)}` (innermost = top level). -/
noncomputable def gtI (b : ℕ → ℝ) : (k : ℕ) → ((Fin k → ℝ) → ENNReal) → ENNReal
  | 0, Φ => Φ (fun i => i.elim0)
  | n + 1, Φ => gtI b n (fun μ => ∫⁻ la in Ilace μ,
      ENNReal.ofReal (posI la * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) * Φ la)

theorem gtI_succ (b : ℕ → ℝ) (n : ℕ) (Φ : (Fin (n + 1) → ℝ) → ENNReal) :
    gtI b (n + 1) Φ = gtI b n (fun μ => ∫⁻ la in Ilace μ,
      ENNReal.ofReal (posI la * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) * Φ la) := rfl

theorem gtI_congr_good (b : ℕ → ℝ) (k : ℕ) (Φ Φ' : (Fin k → ℝ) → ENNReal)
    (h : ∀ μ ∈ Good k, Φ μ = Φ' μ) : gtI b k Φ = gtI b k Φ' := by
  cases k with
  | zero =>
    show Φ _ = Φ' _
    exact h _ ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    rw [gtI_succ, gtI_succ]
    congr 1
    funext μ
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      rw [h la ⟨hsa, fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))⟩]
    · simp [posI, hl]

/-- `∏_{n<k} (M-n-1)!`. -/
noncomputable def Pf (M : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Pf M n * ((M - n - 1).factorial : ℝ)

theorem Pf_pos (M : ℕ) : ∀ k, 0 < Pf M k := by
  intro k
  induction k with
  | zero => show (0 : ℝ) < 1; norm_num
  | succ n ih =>
    show 0 < Pf M n * ((M - n - 1).factorial : ℝ)
    exact mul_pos ih (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- the telescoped top-level density. -/
noncomputable def Dk (M k : ℕ) (la : Fin k → ℝ) : ℝ := vdm la * (∏ i, la i) ^ (M - k) / Pf M k

theorem chain_tele (M : ℕ) (a b : ℕ → ℝ) (hab : ∀ n, a n = b n - 1) :
    ∀ (k : ℕ) (Ψ : (Fin k → ℝ) → ENNReal),
      chain M a k Ψ = gtI b k (fun la => ENNReal.ofReal (Dk M k la) * Ψ la) := by
  intro k
  induction k with
  | zero =>
    intro Ψ
    show Ψ _ = ENNReal.ofReal (Dk M 0 _) * Ψ _
    have : Dk M 0 (fun i => i.elim0) = 1 := by
      unfold Dk vdm
      simp [Pf]
    rw [this, ENNReal.ofReal_one, one_mul]
  | succ n ih =>
    intro Ψ
    rw [chain_succ, ih, gtI_succ]
    apply gtI_congr_good
    rintro μ ⟨hanti, hpos⟩
    have hV : 0 < vdm μ := vdm_pos hanti.injective
    have hA : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hpos i
    have hP := Pf_pos M n
    have hF : (0 : ℝ) < ((M - n - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hP1 : 0 < Pf M (n + 1) := Pf_pos M (n + 1)
    have hD : 0 ≤ Dk M n μ := by
      unfold Dk
      exact div_nonneg (mul_nonneg hV.le (pow_nonneg hA.le _)) hP.le
    have h1 : Dk M n μ * kc M n μ = Real.exp (∑ i, μ i) / Pf M (n + 1) := by
      unfold Dk kc
      show _ = Real.exp (∑ i, μ i) / (Pf M n * ((M - n - 1).factorial : ℝ))
      rw [inv_pow]
      field_simp
    rw [← mul_assoc, ← ENNReal.ofReal_mul hD, h1,
      ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1))) _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      have hlp : ∀ j, 0 < la j := fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))
      have hL : 0 < ∏ j, la j := Finset.prod_pos fun j _ => hlp j
      have hw : wt (M - n - 1) la = Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1) := by
        unfold wt; rw [if_pos hl]
      have hpI : posI la = 1 := by unfold posI; rw [if_pos hl]
      rw [hw, hpI]
      have hA0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) := div_nonneg (Real.exp_pos _).le hP1.le
      have hB0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) * vdm la := mul_nonneg hA0 (vdm_nonneg la)
      have hC0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) * vdm la *
          (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) :=
        mul_nonneg hB0 (mul_nonneg (Real.exp_pos _).le (pow_nonneg hL.le _))
      have hE0 : 0 ≤ (1 : ℝ) * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      have key : ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) * ENNReal.ofReal (vdm la) *
          ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
          ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))) =
          ENNReal.ofReal (1 * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) *
          ENNReal.ofReal (Dk M (n + 1) la) := by
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hC0,
          ← ENNReal.ofReal_mul hE0]
        congr 1
        unfold Dk
        have he : Real.exp (∑ i, μ i) * Real.exp (-∑ j, la j) *
            Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)) = Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) := by
          rw [← Real.exp_add, ← Real.exp_add, hab]
          congr 1
          ring
        rw [show M - (n + 1) = M - n - 1 by omega, ← he]
        ring
      calc ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) *
            (ENNReal.ofReal (vdm la) * Ψ la *
              ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
              ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))))
          = (ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) * ENNReal.ofReal (vdm la) *
              ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
              ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)))) * Ψ la := by ring
        _ = (ENNReal.ofReal (1 * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) *
              ENNReal.ofReal (Dk M (n + 1) la)) * Ψ la := by rw [key]
        _ = _ := by ring
    · simp [wt, posI, hl]

end SWL302

end G0Sec

-- ===== draft (det side)
open MeasureTheory

namespace B4196

open Polynomial in
/-- Child C statement as a Prop. -/
def fredholmDet_finiteRank_stmt : Prop :=
  ∀ (r : ℕ) (φ ψ : Fin r → ℝ → ℝ) (K : ℝ → ℝ → ℝ) (x : ℝ),
    (∀ u v, x < u → x < v → K u v = ∑ a, φ a u * ψ a v) →
    (∀ a b, IntegrableOn (fun u => φ a u * ψ b u) (Set.Ioi x)) →
    SpikedWishart.SoftEdge.fredholmDet K x =
      (1 - Matrix.of fun a b : Fin r => ∫ u in Set.Ioi x, ψ a u * φ b u).det


end B4196

section
open Complex
namespace B4196B

/-- `P(z) = Π_j (π_j - z)`. -/
noncomputable def Pz {N : ℕ} (π : Fin N → ℝ) (z : ℂ) : ℂ := ∏ j, ((π j : ℂ) - z)

/-- z-side factor of the rank-`N` splitting. -/
noncomputable def Ak {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q η : ℝ) (k : Fin N) (z : ℂ) : ℂ :=
  exp (-(η : ℂ) * M * (z - q)) * z ^ M *
    (∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z)) / Pz π z

/-- w-side factor of the rank-`N` splitting. -/
noncomputable def Bk {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q ζ : ℝ) (k : Fin N) (w : ℂ) : ℂ :=
  exp ((ζ : ℂ) * M * (w - q)) * (1 / w ^ M) *
    ∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w)

open ComplexConjugate in
open ComplexConjugate in
open ComplexConjugate in
open ComplexConjugate in
/-- Real z-side functions `α_k(η) = (2πi)⁻¹ ∮_Γ A_k`. -/
noncomputable def alpha {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ : ℝ) (k : Fin N) (η : ℝ) : ℝ :=
  ((2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ), Ak M π q η k z).re

/-- Real w-side functions `β_k(ζ) = (2πi)⁻¹ ∮_Σ B_k`. -/
noncomputable def beta {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cS ρS : ℝ) (k : Fin N) (ζ : ℝ) : ℝ :=
  ((2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w).re

end B4196B
end

section
open MeasureTheory Complex Metric

namespace B4196D

end B4196D

end

section
open MeasureTheory Complex Metric

namespace B4196D
open B4196B

noncomputable def Pa {N : ℕ} (π : Fin N → ℝ) (a : Fin N) : Polynomial ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j => j < a), (Polynomial.C (π j : ℂ) - Polynomial.X)

end B4196D

end


section
open MeasureTheory Complex Metric

end

section
open MeasureTheory Complex Metric

namespace B4196D

end B4196D


namespace B4196D
open B4196B

end B4196D

end


-- ===== G2 + alpha_expand (G4e)
open MeasureTheory Complex Metric
namespace B4196G

/-- box integral of a determinant `det[f_i(μ_k)]` over `Π_k I_k` = determinant of the 1D integrals. -/
theorem integral_box_det {n : ℕ} (f : Fin n → ℝ → ℝ) (I : Fin n → Set ℝ)
    (hf : ∀ i k, IntegrableOn (f i) (I k)) :
    ∫ μ in Set.univ.pi I, (Matrix.of fun i k => f i (μ k)).det =
      (Matrix.of fun i k => ∫ t in I k, f i t).det := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun μ : Fin n → ℝ =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, f (σ k) (μ k)) (Measure.pi fun k => volume.restrict (I k)) := by
    intro σ
    have h1 : Integrable (fun μ : Fin n → ℝ => ∏ k, (fun k t => f (σ k) t) k (μ k))
        (Measure.pi fun k => volume.restrict (I k)) :=
      Integrable.fintype_prod (fun k => hf (σ k) k)
    exact h1.const_mul _
  rw [integral_finset_sum _ (fun σ _ => hint σ)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun k t => f (σ k) t)

/-- bordering: `det[h_i(x_k) - h_i(x_{k+1})]_{i,k<n} = (-1)^n det[[1];[h_i(x_k)]]_{(n+1)×(n+1)}`. -/
theorem det_border {R : Type*} [CommRing R] {n : ℕ} (h : Fin n → Fin (n + 1) → R) :
    (Matrix.of fun (i k : Fin n) => h i k.castSucc - h i k.succ).det =
      (-1) ^ n * (Matrix.of fun (i k : Fin (n + 1)) =>
        (Fin.cases (1 : R) (fun i' => h i' k) i : R)).det := by
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun (i k : Fin (n + 1)) =>
    (Fin.cases (1 : R) (fun i' => h i' k) i : R) with hA
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun j k =>
    (if j = k then 1 else 0) - (if (j : ℕ) = (k : ℕ) + 1 then 1 else 0) with hU
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_lowerTriangular U (fun j k (hjk : j < k) => by
      have h1 : j ≠ k := ne_of_lt hjk
      have h2 : (j : ℕ) ≠ (k : ℕ) + 1 := by have := Fin.lt_def.1 hjk; omega
      simp [hU, h1, h2])]
    refine Finset.prod_eq_one (fun k _ => ?_)
    simp [hU]
  have hcol : ∀ (i k : Fin (n + 1)), (A * U) i k =
      A i k - (if h : (k : ℕ) + 1 < n + 1 then A i ⟨(k : ℕ) + 1, h⟩ else 0) := by
    intro i k
    simp only [Matrix.mul_apply, hU, Matrix.of_apply, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨(k : ℕ) + 1, hk⟩]
      · simp
      · intro m _ hm
        have : (m : ℕ) ≠ (k : ℕ) + 1 := fun e => hm (Fin.ext e)
        simp [this]
      · simp
    · refine Finset.sum_eq_zero (fun m _ => ?_)
      have : (m : ℕ) ≠ (k : ℕ) + 1 := by have := m.isLt; omega
      simp [this]
  have hdet : A.det = (A * U).det := by rw [Matrix.det_mul, hUdet, mul_one]
  rw [hdet, Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin n, (A * U) 0 (Fin.castSucc j) = 0 := by
    intro j
    rw [hcol]
    have hj : (j : ℕ) + 1 < n + 1 := by have := j.isLt; omega
    simp only [Fin.coe_castSucc, hj, dite_true, hA, Matrix.of_apply, Fin.cases_zero, sub_self]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hl : (A * U) 0 (Fin.last n) = 1 := by
    rw [hcol]
    simp [hA]
  rw [hl, mul_one, Fin.val_last, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  congr 1
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last]
  rw [hcol]
  have hk : ((Fin.castSucc k : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
    simp only [Fin.coe_castSucc]; have := k.isLt; omega
  rw [dif_pos hk]
  simp only [hA, Matrix.of_apply, Fin.cases_succ]
  congr 2

section rows
open ComplexConjugate

/-- contour row `(2πi)⁻¹ ∮ e^{-xz} g(z) dz` (complex) and its real part. -/
noncomputable def rowC (g : ℂ → ℂ) (c R : ℝ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((c : ℂ), R), exp (-(x : ℂ) * z) * g z

noncomputable def row (g : ℂ → ℂ) (c R : ℝ) (x : ℝ) : ℝ := (rowC g c R x).re

end rows

section moms
open ComplexConjugate

theorem circ_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral_def_Icc]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add (hf a (Finset.mem_insert_self a s)), ih]
    · exact fun i hi => hf i (Finset.mem_insert_of_mem hi)
    · have : CircleIntegrable (fun z => ∑ i ∈ s, f i z) c R := by
        have h := fun i hi => hf i (Finset.mem_insert_of_mem hi)
        clear ih ha hf
        induction s using Finset.induction_on with
        | empty => simpa using circleIntegrable_const (0 : ℂ) c R
        | insert b t hb ih2 =>
          simp only [Finset.sum_insert hb]
          exact (h b (Finset.mem_insert_self b t)).add
            (ih2 (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      exact this

/-- rows are linear in `g` (real coefficients). -/
theorem row_sum {ι : Type*} (s : Finset ι) (q : ι → ℝ) (g : ι → ℂ → ℂ) (c R : ℝ) (hR : 0 ≤ R)
    (hg : ∀ i ∈ s, ContinuousOn (g i) (sphere (c : ℂ) R)) (x : ℝ) :
    row (fun z => ∑ i ∈ s, (q i : ℂ) * g i z) c R x = ∑ i ∈ s, q i * row (g i) c R x := by
  unfold row rowC
  have e : ∀ z, exp (-(x : ℂ) * z) * ∑ i ∈ s, (q i : ℂ) * g i z =
      ∑ i ∈ s, (q i : ℂ) * (exp (-(x : ℂ) * z) * g i z) := by
    intro z; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
  simp_rw [e]
  rw [circ_finset_sum' s (fun i z => (q i : ℂ) * (exp (-(x : ℂ) * z) * g i z)) _ _
    (fun i hi => ContinuousOn.circleIntegrable hR
    (continuousOn_const.mul (ContinuousOn.mul (by fun_prop) (hg i hi))))]
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [circleIntegral.integral_const_mul, mul_left_comm, Complex.re_ofReal_mul]

variable {N : ℕ}

/-- level-`n` denominator `Π_{j<n} (z - π_j)`. -/
noncomputable def den (π : Fin N → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < n), (z - π j)

/-- level-`n` moment functions `z^{M+i} / den_n(z)`. -/
noncomputable def gm (M : ℕ) (π : Fin N → ℝ) (n i : ℕ) (z : ℂ) : ℂ := z ^ (M + i) / den π n z

noncomputable def momMat (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (n : ℕ) (la : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => row (gm M π n i) c R (la k)

theorem den_ne (π : Fin N → ℝ) (c R : ℝ) (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) (n : ℕ)
    (z : ℂ) (hz : z ∈ sphere (c : ℂ) R) : den π n z ≠ 0 := by
  unfold den
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have h' : z = (π j : ℂ) := sub_eq_zero.1 h
  rw [h'] at hz
  have := hπ j
  rw [mem_ball] at this; rw [mem_sphere] at hz; linarith

theorem gm_cont (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R)
    (n i : ℕ) : ContinuousOn (gm M π n i) (sphere (c : ℂ) R) := by
  unfold gm
  exact ContinuousOn.div (by fun_prop) (by unfold den; fun_prop) (den_ne π c R hπ n)

/-- the real polynomial `Π_{j<n}(X - π_j)`. -/
noncomputable def Qn (π : Fin N → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < n), (Polynomial.X - Polynomial.C (π j))

end moms

section stepsec
variable {N : ℕ}

end stepsec

end B4196G
namespace B4196E
open MeasureTheory Complex Metric B4196G

/-- the real polynomial `Π_{j>b}(π_j - X)`. -/
noncomputable def Qb {N : ℕ} (π : Fin N → ℝ) (b : Fin N) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j => b < j), (Polynomial.C (π j) - Polynomial.X)

theorem Qb_natDegree {N : ℕ} (π : Fin N → ℝ) (b : Fin N) : (Qb π b).natDegree < N := by
  have h1 : (Qb π b).natDegree ≤ (Finset.univ.filter (fun j : Fin N => b < j)).card := by
    calc (Qb π b).natDegree
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => b < j),
            (Polynomial.C (π j) - Polynomial.X).natDegree := by
          unfold Qb; exact Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => b < j), 1 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ = _ := by simp
  have h2 : (Finset.univ.filter (fun j : Fin N => b < j)).card < N := by
    calc (Finset.univ.filter (fun j : Fin N => b < j)).card
        < (Finset.univ : Finset (Fin N)).card :=
          Finset.card_lt_card (Finset.filter_ssubset.2 ⟨b, Finset.mem_univ _, lt_irrefl _⟩)
      _ = N := by simp
  omega

theorem prod_gt_eq_sum {N : ℕ} (π : Fin N → ℝ) (b : Fin N) (z : ℂ) :
    ∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z) =
      ∑ i : Fin N, (((Qb π b).coeff i : ℝ) : ℂ) * z ^ (i : ℕ) := by
  have he : ((Qb π b).map (algebraMap ℝ ℂ)).eval z =
      ∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z) := by
    simp [Qb, Polynomial.map_prod, Polynomial.eval_prod]
  rw [← he, Polynomial.eval_eq_sum_range' (n := N)
    (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Qb_natDegree π b))]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ((Qb π b).map (algebraMap ℝ ℂ)).coeff i * z ^ i) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_map]; rfl

theorem Pz_eq_den {N : ℕ} (π : Fin N → ℝ) (z : ℂ) : B4196B.Pz π z = (-1) ^ N * den π N z := by
  unfold B4196B.Pz den
  have hf : Finset.univ.filter (fun j : Fin N => (j : ℕ) < N) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [hf, show ∏ j : Fin N, ((π j : ℂ) - z) = ∏ j : Fin N, ((-1) * (z - π j)) from
    Finset.prod_congr rfl fun j _ => by ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- E1: `-M α_b(u) = e^{uMq} Σ_i Cf_{b i} m_i(uM)` with moment rows `m_i = row (gm M π N i)`. -/
theorem alpha_expand {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q c R : ℝ) (hR : 0 ≤ R)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) :
    ∃ Cf : Matrix (Fin N) (Fin N) ℝ, ∀ b u, -(M : ℝ) * B4196B.alpha M π q c R b u =
      Real.exp (u * M * q) * ∑ i, Cf b i * row (gm M π N i) c R (u * M) := by
  refine ⟨Matrix.of fun b i => -(M : ℝ) * ((-1) ^ N * (Qb π b).coeff i), fun b u => ?_⟩
  have hpt : ∀ z ∈ sphere (c : ℂ) R, B4196B.Ak M π q u b z =
      ((Real.exp (u * M * q) : ℝ) : ℂ) * (exp (-((u * M : ℝ) : ℂ) * z) *
        ∑ i : Fin N, ((((-1) ^ N * (Qb π b).coeff i : ℝ)) : ℂ) * gm M π N i z) := by
    intro z hz
    have hd := den_ne π c R hπ N z hz
    unfold B4196B.Ak
    have hx : -(u : ℂ) * M * (z - q) = ((u * M * q : ℝ) : ℂ) + -((u * M : ℝ) : ℂ) * z := by
      push_cast; ring
    have hinv : ((-1 : ℂ) ^ N)⁻¹ = (-1) ^ N := by rw [← inv_pow, inv_neg, inv_one]
    rw [prod_gt_eq_sum, Pz_eq_den, Complex.ofReal_exp, hx, Complex.exp_add, div_eq_mul_inv, mul_inv, hinv]
    simp only [gm, div_eq_mul_inv]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
    push_cast
    ring
  have hcirc : (∮ z in C((c : ℂ), R), B4196B.Ak M π q u b z) =
      ((Real.exp (u * M * q) : ℝ) : ℂ) * ∮ z in C((c : ℂ), R), (exp (-((u * M : ℝ) : ℂ) * z) *
        ∑ i : Fin N, ((((-1) ^ N * (Qb π b).coeff i : ℝ)) : ℂ) * gm M π N i z) := by
    rw [circleIntegral.integral_congr hR hpt, circleIntegral.integral_const_mul]
  have hrow := row_sum Finset.univ (fun i : Fin N => (-1) ^ N * (Qb π b).coeff i) (fun i => gm M π N i) c R hR
    (fun i _ => gm_cont M π c R hπ N i) (u * M)
  unfold B4196B.alpha
  rw [hcirc, mul_left_comm, Complex.re_ofReal_mul]
  have hr : ((2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((c : ℂ), R), (exp (-((u * M : ℝ) : ℂ) * z) *
        ∑ i : Fin N, ((((-1) ^ N * (Qb π b).coeff i : ℝ)) : ℂ) * gm M π N i z)).re =
      row (fun z => ∑ i : Fin N, ((((-1) ^ N * (Qb π b).coeff i : ℝ)) : ℂ) * gm M π N i z) c R (u * M) := rfl
  rw [hr, hrow, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.of_apply]
  ring

end B4196E


-- ===== G2w
open MeasureTheory
namespace B4196W
open SpikedWishart.Separated.Lib.Weyl SWL302

theorem measurableSet_Good (k : ℕ) : MeasurableSet (Good k) := by
  have : Good k = (⋂ i : Fin k, ⋂ j : Fin k, ⋂ (_ : i < j), {μ : Fin k → ℝ | μ j < μ i}) ∩
      ⋂ i : Fin k, {μ : Fin k → ℝ | 0 < μ i} := by
    ext μ; simp [Good, StrictAnti]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _))
    (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply _))

theorem measurable_posI (n : ℕ) : Measurable (fun la : Fin (n + 1) → ℝ => posI la) := by
  unfold posI
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply _))
    measurable_const measurable_const

/-- joint set `{(μ, la) | la ∈ Ilace μ}`. -/
theorem measurableSet_IlaceJ (n : ℕ) :
    MeasurableSet {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} := by
  have : {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} =
      ⋂ i : Fin n, ({p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.1 i < p.2 (Fin.castSucc i)} ∩
        {p | p.2 (Fin.succ i) < p.1 i}) := by
    ext p; simp [Ilace]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt ((measurable_pi_apply _).comp measurable_fst)
      ((measurable_pi_apply _).comp measurable_snd)
  · exact measurableSet_lt ((measurable_pi_apply _).comp measurable_snd)
      ((measurable_pi_apply _).comp measurable_fst)

/-- the level weight as a joint function. -/
noncomputable def wJ (b : ℝ) (n : ℕ) (p : (Fin n → ℝ) × (Fin (n + 1) → ℝ)) : ENNReal :=
  ENNReal.ofReal (posI p.2 * Real.exp (-b * (∑ j, p.2 j - ∑ i, p.1 i)))

theorem measurable_wJ (b : ℝ) (n : ℕ) : Measurable (wJ b n) := by
  unfold wJ
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ((measurable_posI n).comp measurable_snd) ?_)
  refine Real.measurable_exp.comp (Measurable.const_mul ?_ _)
  refine Measurable.sub ?_ ?_
  · exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd
  · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst

theorem measurable_inner (b : ℝ) (n : ℕ) (Φ : (Fin (n + 1) → ℝ) → ENNReal) (hΦ : Measurable Φ) :
    Measurable (fun μ : Fin n → ℝ => ∫⁻ la in Ilace μ,
      ENNReal.ofReal (posI la * Real.exp (-b * (∑ j, la j - ∑ i, μ i))) * Φ la) := by
  have hJ : Measurable ({p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1}.indicator
      (fun p => wJ b n p * Φ p.2)) :=
    ((measurable_wJ b n).mul (hΦ.comp measurable_snd)).indicator (measurableSet_IlaceJ n)
  have := hJ.lintegral_prod_right' (ν := (volume : Measure (Fin (n + 1) → ℝ)))
  convert this using 1
  funext μ
  rw [← lintegral_indicator (measurableSet_Ilace μ)]
  refine lintegral_congr fun la => ?_
  by_cases h : la ∈ Ilace μ
  · simp [Set.indicator, h, wJ]
  · simp [Set.indicator, h]

/-- the open interlacing box of `la`. -/
def Bx {n : ℕ} (la : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun k : Fin n => Set.Ioo (la k.succ) (la k.castSucc))

theorem mem_Bx {n : ℕ} (la : Fin (n + 1) → ℝ) (μ : Fin n → ℝ) : μ ∈ Bx la ↔ la ∈ Ilace μ := by
  simp only [Bx, Ilace, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Set.mem_setOf_eq]
  exact forall_congr' fun i => and_comm

theorem measurableSet_Bx {n : ℕ} (la : Fin (n + 1) → ℝ) : MeasurableSet (Bx la) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

theorem Bx_good {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : la ∈ Good (n + 1)) {μ : Fin n → ℝ}
    (hμ : μ ∈ Bx la) : μ ∈ Good n := by
  have hμ' : ∀ k, la k.succ < μ k ∧ μ k < la k.castSucc := fun k => hμ k (Set.mem_univ _)
  refine ⟨fun i j hij => ?_, fun i => lt_trans (hla.2 _) (hμ' i).1⟩
  have hle : Fin.succ i ≤ Fin.castSucc j := by
    rw [Fin.le_def]; simp; exact hij
  exact lt_of_lt_of_le (hμ' j).2 (hla.1.antitone hle) |>.trans (hμ' i).1

theorem Bx_ae {n : ℕ} (la : Fin (n + 1) → ℝ) :
    Bx la =ᵐ[volume] Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)) :=
  by first
    | exact Measure.pi_Ioo_ae_eq_pi_Ioc
    | exact MeasureTheory.pi_Ioo_ae_eq_pi_Ioc
    | exact pi_Ioo_ae_eq_pi_Ioc

theorem Bx_sub_Icc {n : ℕ} (la : Fin (n + 1) → ℝ) :
    Bx la ⊆ Set.Icc (fun k : Fin n => la k.succ) (fun k => la k.castSucc) := by
  intro μ hμ
  exact ⟨fun k => (hμ k (Set.mem_univ _)).1.le, fun k => (hμ k (Set.mem_univ _)).2.le⟩

/-- G2' INDUCTION WRAPPER (generic in the level densities `F n`): the nested GT integral equals
a single integral over the good cone against `c_n F_n`, given the one-level step identity. -/
theorem gt_formula (b : ℕ → ℝ) (F : (n : ℕ) → (Fin n → ℝ) → ℝ) (N : ℕ)
    (hF0 : ∀ x, F 0 x = 1)
    (hFc : ∀ n, Continuous (F n))
    (hstep : ∀ n < N, ∃ C : ℝ, ∀ la : Fin (n + 1) → ℝ, StrictAnti la →
      ∫ μ in Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)),
        Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * F n μ = C * F (n + 1) la) :
    ∀ n ≤ N, ∃ c : ℝ, (∀ la ∈ Good n, 0 ≤ c * F n la) ∧
      ∀ Φ : (Fin n → ℝ) → ENNReal, Measurable Φ →
        gtI b n Φ = ∫⁻ la in Good n, Φ la * ENNReal.ofReal (c * F n la) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨1, fun la _ => by rw [hF0]; norm_num, fun Φ _ => ?_⟩
    show Φ _ = _
    simp only [hF0, mul_one, ENNReal.ofReal_one]
    have hG : Good 0 = Set.univ := by
      ext μ; simp only [Good, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨fun a => a.elim0, fun a => a.elim0⟩
    rw [hG, Measure.restrict_univ, lintegral_unique, volume_pi, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    all_goals congr 1
    all_goals exact Subsingleton.elim _ _
  | succ n ih =>
    intro hn
    obtain ⟨c, hc0, hc⟩ := ih (by omega)
    obtain ⟨C, hC⟩ := hstep n (by omega)
    -- integrand on the box
    set g : (Fin (n + 1) → ℝ) → (Fin n → ℝ) → ℝ := fun la μ =>
      Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * (c * F n μ) with hgdef
    have hgc : ∀ la, Continuous (g la) := by
      intro la
      refine Continuous.mul ?_ (continuous_const.mul (hFc n))
      refine Real.continuous_exp.comp (continuous_const.mul ?_)
      exact continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)
    have hgi : ∀ la, IntegrableOn (g la) (Bx la) := by
      intro la
      exact ((hgc la).continuousOn.integrableOn_compact isCompact_Icc).mono_set (Bx_sub_Icc la)
    have hbox : ∀ la ∈ Good (n + 1), c * C * F (n + 1) la = ∫ μ in Bx la, g la μ := by
      intro la hla
      rw [setIntegral_congr_set (Bx_ae la)]
      have : (fun μ => g la μ) = fun μ => c * (Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * F n μ) := by
        funext μ; simp only [hgdef]; ring
      rw [this, integral_const_mul, hC la hla.1]; ring
    have hgnn : ∀ la ∈ Good (n + 1), ∀ μ ∈ Bx la, 0 ≤ g la μ := fun la hla μ hμ =>
      mul_nonneg (Real.exp_pos _).le (hc0 μ (Bx_good hla hμ))
    refine ⟨c * C, fun la hla => ?_, fun Φ hΦ => ?_⟩
    · rw [hbox la hla]
      exact setIntegral_nonneg (measurableSet_Bx la) (hgnn la hla)
    -- the joint integrand
    set S : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ)) := {p | p.1 ∈ Good n ∧ p.2 ∈ Ilace p.1} with hSdef
    have hS : MeasurableSet S :=
      ((measurableSet_Good n).preimage measurable_fst).inter (measurableSet_IlaceJ n)
    set H : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ENNReal :=
      S.indicator (fun p => wJ (b n) n p * Φ p.2 * ENNReal.ofReal (c * F n p.1)) with hHdef
    have hHm : Measurable H :=
      (((measurable_wJ (b n) n).mul (hΦ.comp measurable_snd)).mul
        (ENNReal.measurable_ofReal.comp (((hFc n).measurable.comp measurable_fst).const_mul c))).indicator hS
    rw [gtI_succ, hc _ (measurable_inner (b n) n Φ hΦ)]
    have hA : ∫⁻ μ in Good n, (∫⁻ la in Ilace μ,
        ENNReal.ofReal (posI la * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) * Φ la) *
          ENNReal.ofReal (c * F n μ) = ∫⁻ μ, ∫⁻ la, H (μ, la) := by
      rw [← lintegral_indicator (measurableSet_Good n)]
      refine lintegral_congr fun μ => ?_
      by_cases hμ : μ ∈ Good n
      · rw [Set.indicator_of_mem hμ, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_indicator (measurableSet_Ilace μ)]
        refine lintegral_congr fun la => ?_
        by_cases h : la ∈ Ilace μ
        · simp [Set.indicator, hHdef, hSdef, hμ, h, wJ]
        · simp [Set.indicator, hHdef, hSdef, h]
      · rw [Set.indicator_of_notMem hμ]
        symm
        refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun la => ?_)
        simp [Set.indicator, hHdef, hSdef, hμ]
    rw [hA, lintegral_lintegral_swap (f := fun μ la => H (μ, la)) hHm.aemeasurable,
      ← lintegral_indicator (measurableSet_Good (n + 1))]
    refine lintegral_congr fun la => ?_
    by_cases hla : la ∈ Good (n + 1)
    · rw [Set.indicator_of_mem hla]
      have hpos : posI la = 1 := by simp [posI, hla.2 (Fin.last n)]
      have hfm : Measurable fun μ : Fin n → ℝ => ENNReal.ofReal (g la μ) :=
        ENNReal.measurable_ofReal.comp (hgc la).measurable
      have h1 : ∀ μ, H (μ, la) = (Bx la).indicator (fun μ => ENNReal.ofReal (g la μ) * Φ la) μ := by
        intro μ
        by_cases hμ : μ ∈ Bx la
        · have hμg := Bx_good hla hμ
          have hil := (mem_Bx la μ).1 hμ
          rw [Set.indicator_of_mem hμ]
          simp only [hHdef, hSdef, Set.indicator, Set.mem_setOf_eq, hμg, hil, and_self, if_true, wJ, hpos,
            one_mul, hgdef]
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
        · rw [Set.indicator_of_notMem hμ]
          have hil : la ∉ Ilace μ := fun h => hμ ((mem_Bx la μ).2 h)
          simp [hHdef, hSdef, Set.indicator, hil]
      simp only [h1]
      rw [lintegral_indicator (measurableSet_Bx la), lintegral_mul_const _ hfm,
        ← ofReal_integral_eq_lintegral_ofReal (hgi la)
          ((ae_restrict_iff' (measurableSet_Bx la)).2 (Filter.Eventually.of_forall (hgnn la hla))),
        ← hbox la hla, mul_comm]
    · rw [Set.indicator_of_notMem hla]
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun μ => ?_)
      show H (μ, la) = 0
      by_cases hm : (μ, la) ∈ S
      · have hil : la ∈ Ilace μ := hm.2
        have hp : posI la = 0 := by
          by_cases hl : 0 < la (Fin.last n)
          · exfalso
            have hsa := ilace_strictAnti hil
            exact hla ⟨hsa, fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))⟩
          · simp [posI, hl]
        simp only [hHdef, Set.indicator_of_mem hm, wJ, hp, zero_mul, ENNReal.ofReal_zero]
      · simp only [hHdef, Set.indicator_of_notMem hm]

end B4196W


-- ===== G3r
open MeasureTheory
namespace B4196R
open SpikedWishart.Separated.Lib.Weyl SWL302

noncomputable def Par {N : ℕ} (π : Fin N → ℝ) (a : Fin N) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j => j < a), (Polynomial.C (π j) - Polynomial.X)

/-- real top-level row functions `B̃_a(y) = Σ_{i<M} [p_a]_i y^{M-1-i}/(M-1-i)!`. -/
noncomputable def Bt (M : ℕ) {N : ℕ} (π : Fin N → ℝ) (a : Fin N) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, (Par π a).coeff i * y ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)

end B4196R


-- ===== G4
open MeasureTheory
namespace B4196S

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

/-- Symmetrization: a symmetric integrable function integrates to `m!` times its integral over
the strictly decreasing chamber. -/
theorem integral_sym {m : ℕ} (g : (Fin m → ℝ) → ℝ) (hg : Integrable g)
    (hsym : ∀ σ : Equiv.Perm (Fin m), ∀ ξ, g (ξ ∘ σ) = g ξ) :
    ∫ ξ, g ξ = (m.factorial : ℝ) * ∫ ξ in SA m, g ξ := by
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
  rw [integral_congr_ae hae, integral_finsetSum _ (fun σ _ => hg.indicator (hS σ))]
  have hone : ∀ σ, ∫ ξ, (S σ).indicator g ξ = ∫ ξ in SA m, g ξ := by
    intro σ
    rw [integral_indicator (hS σ)]
    have he := volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) σ.symm
    rw [hSe, ← he.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) g (SA m)]
    congr 1
    funext ξ
    rw [piCongrLeft_symm_eq, hsym]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end B4196S


-- ===== FC61 A
section FCA


open MeasureTheory Filter Topology Matrix Polynomial

namespace FC61

/-! ## A1: continuity of the sorted eigenvalues -/

theorem antitone_eq_of_prod {n : ℕ} (x y : Fin n → ℝ) (hx : Antitone x) (hy : Antitone y)
    (h : ∀ t : ℝ, ∏ i, (t - x i) = ∏ i, (t - y i)) : x = y := by
  have hp : (∏ i, (X - C (x i)) : ℝ[X]) = ∏ i, (X - C (y i)) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact h t
  have hroot : ∀ z : Fin n → ℝ, (∏ i, (X - C (z i)) : ℝ[X]).roots = Multiset.map z Finset.univ.val := by
    intro z
    rw [Finset.prod_eq_multiset_prod,
      show (fun i => X - C (z i)) = (fun a => X - C a) ∘ z from rfl,
      ← Multiset.map_map (fun a => X - C a) z, roots_multiset_prod_X_sub_C]
  have hr := congrArg Polynomial.roots hp
  rw [hroot, hroot] at hr
  have hs : ∀ z : Fin n → ℝ, Antitone z → (Multiset.map z Finset.univ.val).sort (· ≥ ·) = List.ofFn z := by
    intro z hz
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hz.sortedGE_ofFn
  have := (hs x hx).symm.trans (hr ▸ hs y hy)
  exact List.ofFn_inj.mp this

theorem det_eq_prod_eig0 {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (t : ℂ) :
    (Matrix.scalar (Fin N) t - A).det = ∏ j, (t - ((hA.eigenvalues₀ j : ℝ) : ℂ)) := by
  rw [← Matrix.eval_charpoly, hA.charpoly_eq, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  unfold Matrix.IsHermitian.eigenvalues
  exact Fintype.prod_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm _ _ (fun i => rfl)

theorem abs_eig0_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian) (j) :
    |hA.eigenvalues₀ j| ≤ ∑ a, ∑ b, ‖A a b‖ := by
  set e : Fin (Fintype.card (Fin N)) ≃ Fin N := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))
  have hj : hA.eigenvalues₀ j = hA.eigenvalues (e j) := by
    unfold Matrix.IsHermitian.eigenvalues; simp [e]
  rw [hj, hA.eigenvalues_eq]
  set v := hA.eigenvectorBasis (e j)
  have hv : ∀ a, ‖(v : Fin N → ℂ) a‖ ≤ 1 := by
    intro a
    have h1 := PiLp.norm_apply_le v a
    have h2 : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 _
    rw [h2] at h1
    exact h1
  refine (RCLike.abs_re_le_norm _).trans ?_
  unfold dotProduct Matrix.mulVec dotProduct
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul, Pi.star_apply, norm_star]
  refine (mul_le_mul_of_nonneg_right (hv a) (norm_nonneg _)).trans ?_
  rw [one_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  calc ‖A a b‖ * ‖(v : Fin N → ℂ) b‖ ≤ ‖A a b‖ * 1 := mul_le_mul_of_nonneg_left (hv b) (norm_nonneg _)
    _ = ‖A a b‖ := mul_one _

theorem continuous_eig0 {X : Type*} [MetricSpace X] {N : ℕ} (S : X → Matrix (Fin N) (Fin N) ℂ)
    (hSc : Continuous S) (hS : ∀ x, (S x).IsHermitian) :
    Continuous (fun x => (hS x).eigenvalues₀) := by
  rw [continuous_iff_seqContinuous]
  intro u x hu
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hβc : Continuous (fun x => ∑ a, ∑ b, ‖S x a b‖) := by
    have : ∀ a b, Continuous (fun x => S x a b) := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp hSc)
    fun_prop
  have hβ : Tendsto (fun k => ∑ a, ∑ b, ‖S (u (ns k)) a b‖) atTop (𝓝 (∑ a, ∑ b, ‖S x a b‖)) :=
    (hβc.tendsto x).comp (hu.comp hns)
  obtain ⟨R, hR⟩ := hβ.bddAbove_range
  have hmem : ∀ k, (hS (u (ns k))).eigenvalues₀ ∈ Metric.closedBall (0 : Fin (Fintype.card (Fin N)) → ℝ) R := by
    intro k
    rw [mem_closedBall_zero_iff]
    have hRk : ∑ a, ∑ b, ‖S (u (ns k)) a b‖ ≤ R := hR ⟨k, rfl⟩
    refine pi_norm_le_iff_of_nonneg ((Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      norm_nonneg _).trans hRk) |>.mpr fun j => ?_
    rw [Real.norm_eq_abs]
    exact (abs_eig0_le _ _ j).trans hRk
  obtain ⟨y, -, φ, hφ, hy⟩ := (isCompact_closedBall _ _).tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hyx : y = (hS x).eigenvalues₀ := by
    apply antitone_eq_of_prod
    · intro i j hij
      have hi := (continuous_apply i).continuousAt.tendsto.comp hy
      have hj := (continuous_apply j).continuousAt.tendsto.comp hy
      exact le_of_tendsto_of_tendsto' hj hi fun k => (hS _).eigenvalues₀_antitone hij
    · exact (hS x).eigenvalues₀_antitone
    · intro t
      have h1 : Tendsto (fun k => (Matrix.scalar (Fin N) (t : ℂ) - S (u (ns (φ k)))).det) atTop
          (𝓝 (Matrix.scalar (Fin N) (t : ℂ) - S x).det) := by
        have hc : Continuous (fun x => (Matrix.scalar (Fin N) (t : ℂ) - S x).det) :=
          (continuous_const.sub hSc).matrix_det
        exact (hc.tendsto x).comp ((hu.comp hns).comp hφ.tendsto_atTop)
      have h2 : Tendsto (fun k => (Matrix.scalar (Fin N) (t : ℂ) - S (u (ns (φ k)))).det) atTop
          (𝓝 (∏ j, ((t : ℂ) - ((y j : ℝ) : ℂ)))) := by
        have he : (fun k => (Matrix.scalar (Fin N) (t : ℂ) - S (u (ns (φ k)))).det) =
            fun k => ∏ j, ((t : ℂ) - (((hS (u (ns (φ k)))).eigenvalues₀ j : ℝ) : ℂ)) :=
          funext fun k => det_eq_prod_eig0 _ _ _
        rw [he]
        refine tendsto_finset_prod _ fun j _ => tendsto_const_nhds.sub ?_
        exact (Complex.continuous_ofReal.tendsto _).comp ((continuous_apply j).continuousAt.tendsto.comp hy)
      have h3 := tendsto_nhds_unique h2 h1
      rw [det_eq_prod_eig0 _ (hS x)] at h3
      have h4 : (((∏ j, (t - y j) : ℝ)) : ℂ) = (((∏ j, (t - (hS x).eigenvalues₀ j) : ℝ)) : ℂ) := by
        push_cast; exact h3
      exact Complex.ofReal_injective h4
  rw [hyx] at hy
  exact hy

/-! ## A4: eigenvalues and characteristic polynomials -/

theorem cp_conj {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P ∈ unitaryGroup (Fin N) ℂ) (c : ℂ)
    (W : Matrix (Fin N) (Fin N) ℂ) : (c • (P * W * star P)).charpoly = (c • W).charpoly := by
  have h : star P * P = 1 := mem_unitaryGroup_iff'.mp hP
  rw [show c • (P * W * star P) = P * (c • W * star P) by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc], charpoly_mul_comm,
    Matrix.mul_assoc, h, Matrix.mul_one]

theorem eig_perm_of_charpoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian)
    (x : Fin N → ℝ) (hx : Function.Injective x)
    (hcp : A.charpoly = ∏ j, (X - C ((x j : ℝ) : ℂ))) :
    ∃ σ : Equiv.Perm (Fin N), hA.eigenvalues = x ∘ σ := by
  have hroots : Multiset.map (fun j => ((x j : ℝ) : ℂ)) Finset.univ.val =
      Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← hA.roots_charpoly_eq_eigenvalues, hcp, Finset.prod_eq_multiset_prod,
      show (fun j => X - C ((x j : ℝ) : ℂ)) = (fun a => X - C a) ∘ (fun j => ((x j : ℝ) : ℂ)) from rfl,
      ← Multiset.map_map (fun a => X - C a) (fun j => ((x j : ℝ) : ℂ)), roots_multiset_prod_X_sub_C]
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map] at hre
  have hev : Multiset.map x Finset.univ.val = Multiset.map hA.eigenvalues Finset.univ.val := by
    simpa [Function.comp_def] using hre
  have hnd : (Multiset.map hA.eigenvalues Finset.univ.val).Nodup := by
    rw [← hev]; exact (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mpr (fun a _ b _ hab => hx hab)
  have hevinj : Function.Injective hA.eigenvalues := by
    intro a b hab
    exact (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hnd a (Finset.mem_val.mpr (Finset.mem_univ _)) b
      (Finset.mem_val.mpr (Finset.mem_univ _)) hab
  have hmem : ∀ i, ∃ j, x j = hA.eigenvalues i := by
    intro i
    have : hA.eigenvalues i ∈ Multiset.map x Finset.univ.val := by
      rw [hev]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp this
    exact ⟨j, hj⟩
  choose s hs using hmem
  have hsinj : Function.Injective s := by
    intro a b hab; apply hevinj; rw [← hs a, ← hs b, hab]
  refine ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj), ?_⟩
  funext i
  simp [hs]

/-! ## A2: the exponential Gelfand-Tsetlin step -/

/-- `E_n(la) = det[e^{-b_{n-1-i} la_k}]_{i,k<n}`. -/
noncomputable def EF (b : ℕ → ℝ) (n : ℕ) (la : Fin n → ℝ) : ℝ :=
  (Matrix.of fun (i k : Fin n) => Real.exp (-(b (i.rev : ℕ)) * la k)).det

theorem EF_zero (b : ℕ → ℝ) (x : Fin 0 → ℝ) : EF b 0 x = 1 := Matrix.det_isEmpty

theorem EF_continuous (b : ℕ → ℝ) (n : ℕ) : Continuous (EF b n) := by
  unfold EF
  refine Continuous.matrix_det (continuous_matrix fun i k => ?_)
  fun_prop

theorem integral_exp_Ioc (d : ℝ) (hd : d ≠ 0) (a c : ℝ) (hac : a ≤ c) :
    ∫ t in Set.Ioc a c, Real.exp (d * t) = Real.exp (d * c) / d - Real.exp (d * a) / d := by
  rw [← intervalIntegral.integral_of_le hac]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.exp (d * t) / d)]
  · intro x _
    have h := (((hasDerivAt_id x).const_mul d).exp).div_const d
    simp only [id, mul_one] at h
    rw [mul_div_cancel_right₀ _ hd] at h
    exact h
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- bordering: `det[h_i(x_k) - h_i(x_{k+1})]_{i,k<n} = (-1)^n det[[1];[h_i(x_k)]]_{(n+1)×(n+1)}`. -/
theorem det_border {R : Type*} [CommRing R] {n : ℕ} (h : Fin n → Fin (n + 1) → R) :
    (Matrix.of fun (i k : Fin n) => h i k.castSucc - h i k.succ).det =
      (-1) ^ n * (Matrix.of fun (i k : Fin (n + 1)) =>
        (Fin.cases (1 : R) (fun i' => h i' k) i : R)).det := by
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun (i k : Fin (n + 1)) =>
    (Fin.cases (1 : R) (fun i' => h i' k) i : R) with hA
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun j k =>
    (if j = k then 1 else 0) - (if (j : ℕ) = (k : ℕ) + 1 then 1 else 0) with hU
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_lowerTriangular U (fun j k (hjk : j < k) => by
      have h1 : j ≠ k := ne_of_lt hjk
      have h2 : (j : ℕ) ≠ (k : ℕ) + 1 := by have := Fin.lt_def.1 hjk; omega
      simp [hU, h1, h2])]
    refine Finset.prod_eq_one (fun k _ => ?_)
    simp [hU]
  have hcol : ∀ (i k : Fin (n + 1)), (A * U) i k =
      A i k - (if h : (k : ℕ) + 1 < n + 1 then A i ⟨(k : ℕ) + 1, h⟩ else 0) := by
    intro i k
    simp only [Matrix.mul_apply, hU, Matrix.of_apply, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨(k : ℕ) + 1, hk⟩]
      · simp
      · intro m _ hm
        have : (m : ℕ) ≠ (k : ℕ) + 1 := fun e => hm (Fin.ext e)
        simp [this]
      · simp
    · refine Finset.sum_eq_zero (fun m _ => ?_)
      have : (m : ℕ) ≠ (k : ℕ) + 1 := by have := m.isLt; omega
      simp [this]
  have hdet : A.det = (A * U).det := by rw [Matrix.det_mul, hUdet, mul_one]
  rw [hdet, Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin n, (A * U) 0 (Fin.castSucc j) = 0 := by
    intro j
    rw [hcol]
    have hj : (j : ℕ) + 1 < n + 1 := by have := j.isLt; omega
    simp only [Fin.coe_castSucc, hj, dite_true, hA, Matrix.of_apply, Fin.cases_zero, sub_self]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hl : (A * U) 0 (Fin.last n) = 1 := by
    rw [hcol]
    simp [hA]
  rw [hl, mul_one, Fin.val_last, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  congr 1
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last]
  rw [hcol]
  have hk : ((Fin.castSucc k : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
    simp only [Fin.coe_castSucc]; have := k.isLt; omega
  rw [dif_pos hk]
  simp only [hA, Matrix.of_apply, Fin.cases_succ]
  congr 2

/-- box integral of a determinant `det[f_i(μ_k)]` over `Π_k I_k` = determinant of the 1D integrals. -/
theorem integral_box_det {n : ℕ} (f : Fin n → ℝ → ℝ) (I : Fin n → Set ℝ)
    (hf : ∀ i k, IntegrableOn (f i) (I k)) :
    ∫ μ in Set.univ.pi I, (Matrix.of fun i k => f i (μ k)).det =
      (Matrix.of fun i k => ∫ t in I k, f i t).det := by
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun μ : Fin n → ℝ =>
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, f (σ k) (μ k)) (Measure.pi fun k => volume.restrict (I k)) := by
    intro σ
    have h1 : Integrable (fun μ : Fin n → ℝ => ∏ k, (fun k t => f (σ k) t) k (μ k))
        (Measure.pi fun k => volume.restrict (I k)) :=
      Integrable.fintype_prod (fun k => hf (σ k) k)
    exact h1.const_mul _
  rw [integral_finset_sum _ (fun σ _ => hint σ)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun k t => f (σ k) t)

theorem EF_step (b : ℕ → ℝ) (n : ℕ) (hb : ∀ j < n, b j ≠ b n) :
    ∃ C : ℝ, ∀ la : Fin (n + 1) → ℝ, StrictAnti la →
      ∫ μ in Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)),
        Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * EF b n μ = C * EF b (n + 1) la := by
  set p := b n with hpdef
  set d : Fin n → ℝ := fun i => p - b (i.rev : ℕ) with hd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h
    have hlt : ((i.rev : Fin n) : ℕ) < n := (i.rev).isLt
    exact hb _ hlt (by simp only [hd] at h; linarith)
  refine ⟨(-1) ^ n * ∏ i, (d i)⁻¹, fun la hla => ?_⟩
  have h1 : ∀ μ : Fin n → ℝ, Real.exp (-p * (∑ j, la j - ∑ i, μ i)) * EF b n μ =
      Real.exp (-p * ∑ j, la j) *
        (Matrix.of fun (i k : Fin n) => Real.exp (d i * μ k)).det := by
    intro μ
    have e : (Matrix.of fun (i k : Fin n) => Real.exp (d i * μ k)) =
        Matrix.of fun (i k : Fin n) => (fun k => Real.exp (p * μ k)) k *
          (Matrix.of fun (i k : Fin n) => Real.exp (-(b (i.rev : ℕ)) * μ k)) i k := by
      ext i k
      simp only [Matrix.of_apply, hd, ← Real.exp_add]
      congr 1; ring
    rw [e, Matrix.det_mul_row, ← mul_assoc, ← Real.exp_sum, ← Real.exp_add]
    unfold EF
    congr 2
    rw [Finset.mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  rw [integral_box_det (fun (i : Fin n) t => Real.exp (d i * t)) _
    (fun i k => (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self)]
  set h : Fin n → Fin (n + 1) → ℝ := fun i k => Real.exp (d i * la k) / d i with hh
  have h3 : (Matrix.of fun (i k : Fin n) => ∫ t in Set.Ioc (la k.succ) (la k.castSucc),
      Real.exp (d i * t)) = Matrix.of fun (i k : Fin n) => h i k.castSucc - h i k.succ := by
    ext i k
    have hlt : la k.succ ≤ la k.castSucc := (hla (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
    rw [Matrix.of_apply, integral_exp_Ioc _ (hd0 i) _ _ hlt]
    rfl
  rw [h3, det_border h]
  have h5 : Real.exp (-p * ∑ j, la j) * (Matrix.of fun (i k : Fin (n + 1)) =>
      (Fin.cases (1 : ℝ) (fun i' => h i' k) i : ℝ)).det =
      (∏ i : Fin n, (d i)⁻¹) * EF b (n + 1) la := by
    have e1 : (Matrix.of fun (i k : Fin (n + 1)) => (fun k => Real.exp (-p * la k)) k *
        (Matrix.of fun (i k : Fin (n + 1)) => (Fin.cases (1 : ℝ) (fun i' => h i' k) i : ℝ)) i k) =
        Matrix.of fun (i k : Fin (n + 1)) => (Fin.cases (1 : ℝ) (fun i' => (d i')⁻¹) i : ℝ) *
          (Matrix.of fun (i k : Fin (n + 1)) => Real.exp (-(b (i.rev : ℕ)) * la k)) i k := by
      ext i k
      cases i using Fin.cases with
      | zero =>
        simp only [Matrix.of_apply, Fin.cases_zero, mul_one, one_mul]
        congr 2 <;> simp [hpdef]
      | succ i' =>
        simp only [Matrix.of_apply, Fin.cases_succ, hh, hd]
        have hr : (((Fin.succ i').rev : Fin (n + 1)) : ℕ) = ((i'.rev : Fin n) : ℕ) := by
          simp only [Fin.val_rev, Fin.val_succ]; omega
        rw [hr, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add, mul_comm ((p - b (i'.rev : ℕ))⁻¹)]
        congr 2
        ring
    have e2 := congrArg Matrix.det e1
    have hprod : (∏ i : Fin (n + 1), (Fin.cases (1 : ℝ) (fun i' => (d i')⁻¹) i : ℝ)) =
        ∏ i : Fin n, (d i)⁻¹ := by
      rw [Fin.prod_univ_succ]; simp
    have hexp : (∏ k : Fin (n + 1), Real.exp (-p * la k)) = Real.exp (-p * ∑ j, la j) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    rw [Matrix.det_mul_row, Matrix.det_mul_column, hprod, hexp] at e2
    unfold EF
    exact e2
  rw [← mul_assoc, mul_comm (Real.exp _) ((-1 : ℝ) ^ n), mul_assoc, h5]
  ring

end FC61

end FCA

-- ===== GLUE fc3b9909 (eq_61)
section GlueFC
open MeasureTheory Filter Topology

namespace FC61G
open SpikedWishart.Separated.Lib.Weyl SWL302

theorem Dk_nonneg' (M k : ℕ) (la : Fin k → ℝ) (h : ∀ i, 0 ≤ la i) : 0 ≤ Dk M k la := by
  unfold Dk vdm
  exact div_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (pow_nonneg (Finset.prod_nonneg fun i _ => h i) _)) (Pf_pos M k).le

theorem Dk_continuous' (M k : ℕ) : Continuous (fun la : Fin k → ℝ => Dk M k la) := by
  unfold Dk
  exact (continuous_vdm.mul ((continuous_finset_prod _ fun i _ => continuous_apply i).pow _)).div_const _

theorem eig_congr {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenvalues = hB.eigenvalues := by
  subst h; rfl

/-- the conjugated normalised Wishart matrix `M⁻¹ U W(H) U*`. -/
noncomputable def Tm (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) (H : Fin M → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (M : ℂ)⁻¹ • ((U : Matrix (Fin N) (Fin N) ℂ) * Wm H * star (U : Matrix (Fin N) (Fin N) ℂ))

theorem Tm_eq (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) (H : Fin M → Fin N → ℂ) :
    Tm M N U H = SpikedWishart.SoftEdge.sampleCov M U (fun _ => 1) H := by
  rw [sampleCov_scale]
  unfold Tm
  congr 3
  funext m j
  simp

theorem Tm_herm (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) (H : Fin M → Fin N → ℂ) :
    (Tm M N U H).IsHermitian := by
  rw [Tm_eq]
  exact SpikedWishart.SoftEdge.sampleCov_isHermitian M U _ H

theorem Tm_cont (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) : Continuous (Tm M N U) := by
  unfold Tm
  exact Continuous.const_smul ((continuous_const.matrix_mul (continuous_Wm M N)).matrix_mul continuous_const)
    ((M : ℂ)⁻¹)

noncomputable def ev (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) (H : Fin M → Fin N → ℂ) : Fin N → ℝ :=
  (Tm_herm M N U H).eigenvalues

theorem ev_cont (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) : Continuous (ev M N U) := by
  have h0 := FC61.continuous_eig0 (Tm M N U) (Tm_cont M N U) (Tm_herm M N U)
  unfold ev Matrix.IsHermitian.eigenvalues
  exact continuous_pi fun i => (continuous_apply _).comp h0

theorem ev_left (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) {Q : Matrix (Fin M) (Fin M) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin M) ℂ) (G : Matrix (Fin M) (Fin N) ℂ) :
    ev M N U (Q * G) = ev M N U G :=
  eig_congr _ _ (by unfold Tm; rw [Wm_mul_left hQ G])

theorem ev_right (M N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) {V : Matrix (Fin N) (Fin N) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ) (G : Matrix (Fin M) (Fin N) ℂ) :
    ev M N U (G * V) = ev M N U G := by
  unfold ev
  refine (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hA := Tm_herm M N U (G * V))
    (hB := Tm_herm M N U G)).mpr ?_
  unfold Tm
  rw [Wm_mul_right G V]
  have e : (U : Matrix (Fin N) (Fin N) ℂ) * (Matrix.transpose V * Wm G * star (Matrix.transpose V)) *
      star (U : Matrix (Fin N) (Fin N) ℂ) =
      ((U : Matrix (Fin N) (Fin N) ℂ) * Matrix.transpose V) * Wm G *
        star ((U : Matrix (Fin N) (Fin N) ℂ) * Matrix.transpose V) := by
    rw [star_mul]; simp only [Matrix.mul_assoc]
  rw [e, FC61.cp_conj _ (Submonoid.mul_mem _ U.2 (transpose_mem_unitary hV)), FC61.cp_conj _ U.2]

theorem ev_emb (M N : ℕ) (hM : 0 < M) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (la : Fin N → ℝ) (hla : la ∈ Good N) :
    ∃ σ : Equiv.Perm (Fin N), ev M N U (Emb M N la) = (fun i => la i / M) ∘ σ := by
  have hx : Function.Injective (fun i => la i / (M : ℝ)) := by
    intro i j h
    have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    exact hla.1.injective (by simpa [div_left_inj' hM'.ne'] using h)
  refine FC61.eig_perm_of_charpoly _ _ _ hx ?_
  unfold Tm
  rw [Wm_Emb hNM la (fun j => (hla.2 j).le), FC61.cp_conj _ U.2, ← Matrix.diagonal_smul,
    Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- (I) the eigenvalue law as a weighted integral over the chamber `Good N` (unnormalised). -/
theorem lint_eq (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (π : Fin N → ℝ) (hπ0 : ∀ i, 0 < π i) (hπinj : Function.Injective π) :
    ∃ c : ℝ, (∀ la ∈ Good N, 0 ≤ c * FC61.EF (fun n => aπ π n + 1) N la) ∧
      ∀ Ψ : (Fin N → ℝ) → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
        (∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), Ψ (x ∘ σ) = Ψ x) →
        ∫⁻ G, ENNReal.ofReal (Ψ (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
            (fun i => (π i)⁻¹) G).eigenvalues) ∂(SpikedWishart.SoftEdge.sampleLaw M N) =
          (∏ i, ENNReal.ofReal (π i ^ M)) * ∫⁻ la in Good N, ENNReal.ofReal (Ψ (fun i => la i / M) *
            (Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la))) := by
  haveI : NeZero N := ⟨by omega⟩
  have hM : 0 < M := by omega
  rw [show SpikedWishart.SoftEdge.sampleLaw M N = SpikedWishart.FixedDim.sampleLaw M N from rfl]
  set b : ℕ → ℝ := fun n => aπ π n + 1 with hbdef
  have hbN : ∀ j (hj : j < N), b j = π ⟨j, hj⟩ := by
    intro j hj
    simp [hbdef, aπ, hj]
  have hstep : ∀ n < N, ∃ C : ℝ, ∀ la : Fin (n + 1) → ℝ, StrictAnti la →
      ∫ μ in Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)),
        Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * FC61.EF b n μ = C * FC61.EF b (n + 1) la := by
    intro n hn
    refine FC61.EF_step b n fun j hj h => ?_
    rw [hbN j (by omega), hbN n hn] at h
    have := hπinj h
    simp only [Fin.mk.injEq] at this
    omega
  obtain ⟨cN, hcN0, hcN⟩ := B4196W.gt_formula b (fun n => FC61.EF b n) N (FC61.EF_zero b)
    (FC61.EF_continuous b) hstep N le_rfl
  refine ⟨cN, hcN0, fun Ψ hΨ hΨ0 hΨs => ?_⟩
  set Fz : (Fin M → Fin N → ℂ) → ENNReal := fun H => ENNReal.ofReal (Ψ (ev M N U H)) with hFzdef
  have hFz : Measurable Fz := ENNReal.measurable_ofReal.comp (hΨ.comp (ev_cont M N U).measurable)
  have h1 : ∀ G : Fin M → Fin N → ℂ, ENNReal.ofReal (Ψ (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
      (fun i => (π i)⁻¹) G).eigenvalues) =
      Fz (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
    intro G
    simp only [hFzdef, ev]
    congr 2
    exact eig_congr _ _ (by rw [sampleCov_scale]; rfl)
  rw [lintegral_congr h1, lintegral_scale π hπ0 Fz hFz]
  simp_rw [sclW_eq π hπ0]
  have h2 : ∀ G : Fin M → Fin N → ℂ, (∏ j, ENNReal.ofReal (π j ^ M)) * colW (aπ π) G * Fz G =
      (∏ j, ENNReal.ofReal (π j ^ M)) * (Fz G * colW (aπ π) G) := fun G => by ring
  rw [lintegral_congr h2, lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top)]
  congr 1
  rw [nw_all M N hNM (aπ π) Fz hFz
    (fun Q hQ G => by simp only [hFzdef]; rw [ev_left M N U hQ G])
    (fun V hV G => by simp only [hFzdef]; rw [ev_right M N U hV G])]
  rw [chain_congr_good M (aπ π) N _ (fun la => ENNReal.ofReal (Ψ (fun i => la i / M))) (fun la hla => by
    obtain ⟨σ, hσ⟩ := ev_emb M N hM hNM U la hla
    simp only [hFzdef]
    rw [hσ, hΨs])]
  rw [chain_tele M (aπ π) b (fun n => by simp [hbdef]) N]
  have hΦ : Measurable (fun la : Fin N → ℝ => ENNReal.ofReal (Dk M N la) *
      ENNReal.ofReal (Ψ (fun i => la i / M))) :=
    (ENNReal.measurable_ofReal.comp (Dk_continuous' M N).measurable).mul
      (ENNReal.measurable_ofReal.comp (hΨ.comp (by fun_prop)))
  rw [hcN _ hΦ]
  refine setLIntegral_congr_fun (B4196W.measurableSet_Good N) (fun la hla => ?_)
  rw [ENNReal.ofReal_mul (hΨ0 _), ENNReal.ofReal_mul (Dk_nonneg' M N la fun i => (hla.2 i).le)]
  ring

/-- (I') the real form: `∫ g(eig) dP = K ∫_{Good} g(la/M) W(la)`, with `W ≥ 0` integrable on `Good`. -/
theorem real_eq (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (π : Fin N → ℝ) (hπ0 : ∀ i, 0 < π i) (hπinj : Function.Injective π) :
    ∃ c : ℝ, IntegrableOn (fun la => Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la)) (Good N) ∧
      ∀ g : (Fin N → ℝ) → ℝ, Measurable g → (∃ B : ℝ, ∀ x, |g x| ≤ B) →
        (∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), g (x ∘ σ) = g x) →
        ∫ G, g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
            (fun i => (π i)⁻¹) G).eigenvalues ∂(SpikedWishart.SoftEdge.sampleLaw M N) =
          (∏ i, π i ^ M) * ∫ la in Good N, g (fun i => la i / M) *
            (Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la)) := by
  haveI : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M N) := by
    show IsProbabilityMeasure (SpikedWishart.FixedDim.sampleLaw M N)
    infer_instance
  obtain ⟨c, hc0, hL⟩ := lint_eq M N hN hNM U π hπ0 hπinj
  set W : (Fin N → ℝ) → ℝ := fun la => Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la) with hWdef
  have hW0 : ∀ la ∈ Good N, 0 ≤ W la := fun la hla =>
    mul_nonneg (Dk_nonneg' M N la fun i => (hla.2 i).le) (hc0 la hla)
  have hWc : Continuous W :=
    (Dk_continuous' M N).mul (continuous_const.mul (FC61.EF_continuous _ N))
  set K : ℝ := ∏ i, π i ^ M with hKdef
  have hK0 : 0 < K := Finset.prod_pos fun i _ => pow_pos (hπ0 i) M
  have hKe : (∏ i, ENNReal.ofReal (π i ^ M)) = ENNReal.ofReal K := by
    rw [hKdef, ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hπ0 i).le M)]
  have hGood := B4196W.measurableSet_Good N
  have hW0ae : 0 ≤ᵐ[volume.restrict (Good N)] W :=
    (ae_restrict_iff' hGood).2 (Filter.Eventually.of_forall hW0)
  -- integrability of W from Ψ = 1
  have hone := hL (fun _ => 1) measurable_const (fun _ => zero_le_one) (fun _ _ => rfl)
  simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, one_mul, hKe] at hone
  have hfin : ∫⁻ la in Good N, ENNReal.ofReal (W la) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hK0)] at hone
    exact ENNReal.top_ne_one hone.symm
  have hWint : IntegrableOn W (Good N) :=
    ⟨hWc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hW0ae).2 hfin⟩
  refine ⟨c, hWint, ?_⟩
  -- nonnegative bounded case
  have hpos : ∀ Ψ : (Fin N → ℝ) → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x, Ψ x ≤ 1 + |Ψ x|) →
      (∃ B : ℝ, ∀ x, Ψ x ≤ B) →
      (∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), Ψ (x ∘ σ) = Ψ x) →
      ∫ G, Ψ (SpikedWishart.SoftEdge.sampleCov_isHermitian M U (fun i => (π i)⁻¹) G).eigenvalues
          ∂(SpikedWishart.SoftEdge.sampleLaw M N) =
        K * ∫ la in Good N, Ψ (fun i => la i / M) * W la := by
    intro Ψ hΨ hΨ0 _ ⟨B, hB⟩ hΨs
    have hmeasG : Measurable (fun G : Fin M → Fin N → ℂ => Ψ (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
        (fun i => (π i)⁻¹) G).eigenvalues) := by
      have : (fun G : Fin M → Fin N → ℂ => (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
          (fun i => (π i)⁻¹) G).eigenvalues) =
          fun G => ev M N U (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
        funext G
        exact eig_congr _ _ (by rw [sampleCov_scale]; rfl)
      have hev : Measurable (fun G : Fin M → Fin N → ℂ => (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
          (fun i => (π i)⁻¹) G).eigenvalues) := by
        rw [this]; exact (ev_cont M N U).measurable.comp (by fun_prop)
      exact hΨ.comp hev
    have hintG : Integrable (fun G : Fin M → Fin N → ℂ => Ψ (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
        (fun i => (π i)⁻¹) G).eigenvalues) (SpikedWishart.SoftEdge.sampleLaw M N) :=
      (integrable_const B).mono' hmeasG.aestronglyMeasurable
        (Filter.Eventually.of_forall fun G => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 _)]; exact hB _)
    have hmeasL : Measurable (fun la : Fin N → ℝ => Ψ (fun i => la i / M)) := hΨ.comp (by fun_prop)
    have hintL : IntegrableOn (fun la => Ψ (fun i => la i / M) * W la) (Good N) :=
      hWint.bdd_mul hmeasL.aestronglyMeasurable
        (Filter.Eventually.of_forall fun la => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 _)]; exact hB _)
    have hL' := hL Ψ hΨ hΨ0 hΨs
    rw [hKe, ← ofReal_integral_eq_lintegral_ofReal hintG (Filter.Eventually.of_forall fun G => hΨ0 _),
      ← ofReal_integral_eq_lintegral_ofReal hintL
        ((ae_restrict_iff' hGood).2 (Filter.Eventually.of_forall fun la hla =>
          mul_nonneg (hΨ0 _) (hW0 la hla))),
      ← ENNReal.ofReal_mul hK0.le] at hL'
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun G => hΨ0 _)
      (mul_nonneg hK0.le (setIntegral_nonneg hGood fun la hla => mul_nonneg (hΨ0 _) (hW0 la hla)))).1 hL'
  intro g hg ⟨B, hB⟩ hgs
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have e1 := hpos (fun x => g x + B) (hg.add measurable_const)
    (fun x => by have := neg_abs_le (g x); linarith [hB x])
    (fun x => by have := le_abs_self (g x + B); linarith)
    ⟨2 * B, fun x => by have := le_abs_self (g x); linarith [hB x]⟩
    (fun σ x => by simp only [hgs])
  have e2 := hpos (fun _ => B) measurable_const (fun _ => hB0)
    (fun x => by have := le_abs_self B; linarith) ⟨B, fun _ => le_rfl⟩ (fun _ _ => rfl)
  have hmeasG : Measurable (fun G : Fin M → Fin N → ℂ => g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
      (fun i => (π i)⁻¹) G).eigenvalues) := by
    have : (fun G : Fin M → Fin N → ℂ => (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
        (fun i => (π i)⁻¹) G).eigenvalues) =
        fun G => ev M N U (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
      funext G
      exact eig_congr _ _ (by rw [sampleCov_scale]; rfl)
    have hev : Measurable (fun G : Fin M → Fin N → ℂ => (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
        (fun i => (π i)⁻¹) G).eigenvalues) := by
      rw [this]; exact (ev_cont M N U).measurable.comp (by fun_prop)
    exact hg.comp hev
  have hintG : Integrable (fun G : Fin M → Fin N → ℂ => g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
      (fun i => (π i)⁻¹) G).eigenvalues) (SpikedWishart.SoftEdge.sampleLaw M N) :=
    (integrable_const B).mono' hmeasG.aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => by rw [Real.norm_eq_abs]; exact hB _)
  have hmeasL : Measurable (fun la : Fin N → ℝ => g (fun i => la i / M)) := hg.comp (by fun_prop)
  have hintL : IntegrableOn (fun la => g (fun i => la i / M) * W la) (Good N) :=
    hWint.bdd_mul hmeasL.aestronglyMeasurable
      (Filter.Eventually.of_forall fun la => by rw [Real.norm_eq_abs]; exact hB _)
  have hintBW : IntegrableOn (fun la => B * W la) (Good N) := hWint.const_mul B
  rw [integral_add hintG (integrable_const B), integral_const, setIntegral_congr_fun hGood
    (fun la _ => add_mul (g (fun i => la i / M)) B (W la)), integral_add hintL hintBW] at e1
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at e1 e2
  rw [integral_const, probReal_univ, one_smul] at e2
  show _ = K * ∫ la in Good N, g (fun i => la i / M) * W la
  rw [mul_add] at e1
  linarith

/-- the chamber is invariant under `x ↦ x/M`. -/
theorem good_div (M N : ℕ) (hM : 0 < M) (x : Fin N → ℝ) :
    (fun i => x i / (M : ℝ)) ∈ Good N ↔ x ∈ Good N := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h1 hij
      simp only at this
      exact (div_lt_div_iff_of_pos_right hM').1 this
    · exact (div_pos_iff_of_pos_right hM').1 (h2 i)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => div_pos (h2 i) hM'⟩
    exact (div_lt_div_iff_of_pos_right hM').2 (h1 hij)

/-- (II) change of variables `la = M λ` on the chamber. -/
theorem cov (M N : ℕ) (hM : 0 < M) (h : (Fin N → ℝ) → ℝ) :
    ∫ la in Good N, h (fun i => la i / M) = (M : ℝ) ^ N * ∫ x in Good N, h x := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  rw [← integral_indicator (B4196W.measurableSet_Good N), ← integral_indicator (B4196W.measurableSet_Good N)]
  have e : (Good N).indicator (fun la => h (fun i => la i / M)) =
      fun la => (Good N).indicator h (((M : ℝ)⁻¹) • la) := by
    funext la
    have hs : ((M : ℝ)⁻¹ • la) = fun i => la i / M := by
      funext i; simp [div_eq_inv_mul]
    rw [hs]
    by_cases hla : la ∈ Good N
    · rw [Set.indicator_of_mem hla, Set.indicator_of_mem ((good_div M N hM la).2 hla)]
    · rw [Set.indicator_of_notMem hla, Set.indicator_of_notMem (fun h' => hla ((good_div M N hM la).1 h'))]
  rw [e, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (pow_pos hM' N)]

/-- symmetrization for nonnegative functions. -/
theorem lintegral_sym {m : ℕ} (g : (Fin m → ℝ) → ENNReal) (hg : Measurable g)
    (hsym : ∀ σ : Equiv.Perm (Fin m), ∀ ξ, g (ξ ∘ σ) = g ξ) :
    ∫⁻ ξ, g ξ = (m.factorial : ENNReal) * ∫⁻ ξ in B4196S.SA m, g ξ := by
  classical
  set S : Equiv.Perm (Fin m) → Set (Fin m → ℝ) := fun σ => {ξ | StrictAnti (ξ ∘ σ)} with hSdef
  have hSe : ∀ σ, S σ = (MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) σ.symm) ⁻¹' B4196S.SA m := by
    intro σ; ext ξ; simp [hSdef, B4196S.SA, B4196S.piCongrLeft_symm_eq]
  have hS : ∀ σ, MeasurableSet (S σ) := by
    intro σ; rw [hSe]; exact (MeasurableEquiv.measurable _) (B4196S.measurableSet_SA m)
  have hinj : ∀ᵐ ξ ∂(volume : Measure (Fin m → ℝ)), Function.Injective ξ := by
    rw [ae_iff]; exact B4196S.null_not_inj m
  have hae : (fun ξ => g ξ) =ᵐ[volume] fun ξ => ∑ σ, (S σ).indicator g ξ := by
    filter_upwards [hinj] with ξ hξ
    rw [Finset.sum_eq_single (Tuple.sort (fun i => -ξ i))]
    · rw [Set.indicator_of_mem]; exact B4196S.strictAnti_sort hξ
    · intro τ _ hτ
      rw [Set.indicator_of_notMem]
      intro hmem; exact hτ (B4196S.eq_sort_of_strictAnti hmem)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [lintegral_congr_ae hae, lintegral_finset_sum _ (fun σ _ => hg.indicator (hS σ))]
  have hone : ∀ σ, ∫⁻ ξ, (S σ).indicator g ξ = ∫⁻ ξ in B4196S.SA m, g ξ := by
    intro σ
    rw [lintegral_indicator (hS σ)]
    have he := volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) σ.symm
    rw [hSe, ← he.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _) g (B4196S.SA m)]
    congr 1
    funext ξ
    rw [B4196S.piCongrLeft_symm_eq, hsym]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

/-- the positive orthant. -/
def Ort (N : ℕ) : Set (Fin N → ℝ) := Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ))

theorem measurableSet_Ort (N : ℕ) : MeasurableSet (Ort N) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

theorem ort_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) : x ∘ σ ∈ Ort N ↔ x ∈ Ort N := by
  simp only [Ort, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, true_implies, Function.comp]
  constructor
  · intro h i; have := h (σ.symm i); simpa using this
  · intro h i; exact h (σ i)

theorem SA_inter_Ort (N : ℕ) : B4196S.SA N ∩ Ort N = Good N := by
  ext x
  simp [B4196S.SA, Ort, Good, Set.mem_pi]

theorem eigDensity_sym (M N : ℕ) (π : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ) :
    SpikedWishart.SoftEdge.eigDensity M π (x ∘ σ) = SpikedWishart.SoftEdge.eigDensity M π x := by
  unfold SpikedWishart.SoftEdge.eigDensity
  have h1 : (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * (x ∘ σ) k)).det =
      (Equiv.Perm.sign σ : ℝ) * (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * x k)).det := by
    rw [← Matrix.det_permute']
    rfl
  have h2 : (Matrix.vandermonde (x ∘ σ)).det = (Equiv.Perm.sign σ : ℝ) * (Matrix.vandermonde x).det := by
    rw [← Matrix.det_permute]
    rfl
  have h3 : ∏ j, (x ∘ σ) j ^ (M - N) = ∏ j, x j ^ (M - N) :=
    Equiv.prod_comp σ (fun j => x j ^ (M - N))
  rw [h1, h2, h3]
  have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  calc (Equiv.Perm.sign σ : ℝ) * (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * x k)).det /
        (Matrix.vandermonde π).det * ((Equiv.Perm.sign σ : ℝ) * (Matrix.vandermonde x).det) *
        ∏ j, x j ^ (M - N)
      = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ)) *
        ((Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * x k)).det / (Matrix.vandermonde π).det *
          (Matrix.vandermonde x).det * ∏ j, x j ^ (M - N)) := by push_cast; ring
    _ = _ := by rw [hs, one_mul]

theorem eigDensity_cont (M N : ℕ) (π : Fin N → ℝ) :
    Continuous (SpikedWishart.SoftEdge.eigDensity M π) := by
  unfold SpikedWishart.SoftEdge.eigDensity
  have h1 : Continuous (fun x : Fin N → ℝ => (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * x k)).det) :=
    Continuous.matrix_det (continuous_matrix fun j k => by fun_prop)
  have h2 : Continuous (fun x : Fin N → ℝ => (Matrix.vandermonde x).det) :=
    Continuous.matrix_det (continuous_matrix fun i j => by
      simp only [Matrix.vandermonde_apply]; fun_prop)
  exact ((h1.div_const _).mul h2).mul (continuous_finset_prod _ fun j _ => (continuous_apply j).pow _)

/-- the chamber density `W` is a constant multiple of `eigDensity(la/M)`. -/
theorem dens_eq (M N : ℕ) (hM : 0 < M) (π : Fin N → ℝ) (hπinj : Function.Injective π) (c : ℝ) :
    ∃ κ : ℝ, ∀ la ∈ Good N, Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la) =
      κ * SpikedWishart.SoftEdge.eigDensity M π (fun k => la k / M) := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hVπ : (Matrix.vandermonde π).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hπinj
  set s : ℝ := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ) with hs
  set Q1 : ℝ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (-(M : ℝ)) with hQ1
  set Q2 : ℝ := ((M : ℝ) ^ N) ^ (M - N) with hQ2
  refine ⟨c * s * Q1 * Q2 / Pf M N * (Matrix.vandermonde π).det, fun la hla => ?_⟩
  have hE : FC61.EF (fun n => aπ π n + 1) N la =
      s * (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * (la k / M))).det := by
    rw [hs, ← Matrix.det_permute]
    unfold FC61.EF
    congr 1
    ext i k
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply]
    have hr : aπ π ((i.rev : Fin N) : ℕ) + 1 = π i.rev := by rw [aπ_fin]; ring
    rw [hr]
    congr 1
    field_simp
  have hV : vdm la = Q1 * (Matrix.vandermonde (fun k => la k / M)).det := by
    rw [Matrix.det_vandermonde, hQ1, ← Finset.prod_mul_distrib]
    unfold vdm
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : la j < la i := hla.1 hij
    rw [abs_of_pos (by linarith)]
    field_simp
    ring
  have hP : (∏ i, la i) ^ (M - N) = Q2 * ∏ j, (la j / M) ^ (M - N) := by
    have e : ∏ i, la i = (M : ℝ) ^ N * ∏ i, (la i / M) := by
      rw [show (M : ℝ) ^ N = ∏ _i : Fin N, (M : ℝ) by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      field_simp
    rw [e, mul_pow, Finset.prod_pow]
  have hPf : Pf M N ≠ 0 := (Pf_pos M N).ne'
  unfold Dk SpikedWishart.SoftEdge.eigDensity
  rw [hE, hV, hP]
  field_simp
  try ring

/-- symmetrization of a set integral over the orthant. -/
theorem ort_integral (N : ℕ) (g : (Fin N → ℝ) → ℝ) (hg : IntegrableOn g (Ort N))
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), g (x ∘ σ) = g x) :
    ∫ x in Ort N, g x = (N.factorial : ℝ) * ∫ x in Good N, g x := by
  rw [← integral_indicator (measurableSet_Ort N),
    B4196S.integral_sym _ (hg.integrable_indicator (measurableSet_Ort N)) (fun σ x => by
      by_cases hx : x ∈ Ort N
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((ort_perm σ x).2 hx), hsym]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((ort_perm σ x).1 h))]),
    setIntegral_indicator (measurableSet_Ort N), SA_inter_Ort]

/-- KEY: `∫ g(eig) dP = A ∫_{(0,∞)^N} g p` for one constant `A`, all bounded measurable symmetric `g`. -/
theorem key (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (π : Fin N → ℝ) (hπ0 : ∀ i, 0 < π i) (hπinj : Function.Injective π) :
    ∃ A : ℝ, IntegrableOn (SpikedWishart.SoftEdge.eigDensity M π) (Ort N) ∧
      ∀ g : (Fin N → ℝ) → ℝ, Measurable g → (∃ B : ℝ, ∀ x, |g x| ≤ B) →
        (∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), g (x ∘ σ) = g x) →
        ∫ G, g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U
            (fun i => (π i)⁻¹) G).eigenvalues ∂(SpikedWishart.SoftEdge.sampleLaw M N) =
          A * ∫ x in Ort N, g x * SpikedWishart.SoftEdge.eigDensity M π x := by
  haveI : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M N) := by
    show IsProbabilityMeasure (SpikedWishart.FixedDim.sampleLaw M N)
    infer_instance
  have hM : 0 < M := by omega
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨c, hWint, hR⟩ := real_eq M N hN hNM U π hπ0 hπinj
  obtain ⟨κ, hκ⟩ := dens_eq M N hM π hπinj c
  set p := SpikedWishart.SoftEdge.eigDensity M π with hpdef
  set K : ℝ := ∏ i, π i ^ M with hKdef
  have hGood := B4196W.measurableSet_Good N
  -- every chamber integral in `la` becomes `κ M^N ∫_{Good} g p`
  have hstep : ∀ g : (Fin N → ℝ) → ℝ, ∫ la in Good N, g (fun i => la i / M) *
      (Dk M N la * (c * FC61.EF (fun n => aπ π n + 1) N la)) =
      κ * ((M : ℝ) ^ N * ∫ x in Good N, g x * p x) := by
    intro g
    rw [setIntegral_congr_fun hGood (fun la hla => by rw [hκ la hla]), ← cov M N hM (fun x => g x * p x),
      ← integral_const_mul]
    refine setIntegral_congr_fun hGood fun la _ => ?_
    ring
  -- κ ≠ 0 from total mass one
  have h1 := hR (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩ (fun _ _ => rfl)
  have h1' := hstep (fun _ => 1)
  beta_reduce at h1'
  rw [integral_const, probReal_univ, one_smul, h1'] at h1
  have hκ0 : κ ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  -- integrability of p on the chamber, then on the orthant
  have hpGood : IntegrableOn p (Good N) := by
    have h2 : Integrable (fun x => (Good N).indicator (fun la => Dk M N la *
        (c * FC61.EF (fun n => aπ π n + 1) N la)) ((M : ℝ) • x)) :=
      (hWint.integrable_indicator hGood).comp_smul hM'.ne'
    have h3 : (fun x => (Good N).indicator (fun la => Dk M N la *
        (c * FC61.EF (fun n => aπ π n + 1) N la)) ((M : ℝ) • x)) =
        (Good N).indicator (fun x => κ * p x) := by
      funext x
      have hs : (fun k => ((M : ℝ) • x) k / M) = x := by
        funext k; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
      have hmem : (M : ℝ) • x ∈ Good N ↔ x ∈ Good N := by
        rw [← good_div M N hM, hs]
      by_cases hx : x ∈ Good N
      · rw [Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx, hκ _ (hmem.2 hx), hs]
      · rw [Set.indicator_of_notMem (fun h => hx (hmem.1 h)), Set.indicator_of_notMem hx]
    rw [h3, integrable_indicator_iff hGood] at h2
    have h4 := h2.const_mul κ⁻¹
    exact IntegrableOn.congr_fun h4 (fun x _ => by field_simp) hGood
  have hpc := eigDensity_cont M N π
  have hpOrt : IntegrableOn p (Ort N) := by
    refine ⟨hpc.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in Ort N, ‖p x‖ₑ < ⊤
    rw [← lintegral_indicator (measurableSet_Ort N),
      lintegral_sym _ ((hpc.measurable.enorm).indicator (measurableSet_Ort N)) (fun σ x => by
        by_cases hx : x ∈ Ort N
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((ort_perm σ x).2 hx),
            eigDensity_sym]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((ort_perm σ x).1 h))]),
      setLIntegral_indicator (measurableSet_Ort N), Set.inter_comm, SA_inter_Ort]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hpGood.2
  refine ⟨K * κ * (M : ℝ) ^ N / (N.factorial : ℝ), hpOrt, fun g hg ⟨B, hB⟩ hgs => ?_⟩
  rw [hR g hg ⟨B, hB⟩ hgs, hstep, ort_integral N (fun x => g x * p x)
    (hpOrt.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hB x))
    (fun σ x => by simp only [hgs, hpdef, eigDensity_sym])]
  have hf : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  field_simp

theorem main (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j) (hℓ_inj : Function.Injective ℓ)
    (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) (hf_bdd : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hf_sym : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x) :
    ∫ G, f (SpikedWishart.SoftEdge.sampleCov_isHermitian M U ℓ G).eigenvalues
        ∂(SpikedWishart.SoftEdge.sampleLaw M N) =
      (∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          f lam * SpikedWishart.SoftEdge.eigDensity M (fun j => (ℓ j)⁻¹) lam) /
        ∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          SpikedWishart.SoftEdge.eigDensity M (fun j => (ℓ j)⁻¹) lam := by
  haveI : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M N) := by
    show IsProbabilityMeasure (SpikedWishart.FixedDim.sampleLaw M N)
    infer_instance
  set π : Fin N → ℝ := fun j => (ℓ j)⁻¹ with hπdef
  have hπ0 : ∀ i, 0 < π i := fun i => inv_pos.2 (hℓ i)
  have hπinj : Function.Injective π := fun i j h => hℓ_inj (inv_injective h)
  have hinv : (fun i => (π i)⁻¹) = ℓ := funext fun i => inv_inv _
  obtain ⟨A, -, hA⟩ := key M N hN hNM U π hπ0 hπinj
  have hconv : ∀ g : (Fin N → ℝ) → ℝ, (fun G => g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U ℓ G).eigenvalues) =
      fun G => g (SpikedWishart.SoftEdge.sampleCov_isHermitian M U (fun i => (π i)⁻¹) G).eigenvalues := by
    intro g; funext G; congr 1; exact eig_congr _ _ (by rw [hinv])
  have h1 := hA (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩ (fun _ _ => rfl)
  rw [integral_const, probReal_univ, one_smul] at h1
  simp only [one_mul] at h1
  have hI : (∫ x in Ort N, SpikedWishart.SoftEdge.eigDensity M π x) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact one_ne_zero h1
  have hf' := hA f hf hf_bdd hf_sym
  rw [← hconv f] at hf'
  rw [hf']
  show A * ∫ x in Ort N, f x * SpikedWishart.SoftEdge.eigDensity M π x =
    (∫ x in Ort N, f x * SpikedWishart.SoftEdge.eigDensity M π x) /
      ∫ x in Ort N, SpikedWishart.SoftEdge.eigDensity M π x
  rw [eq_div_iff hI]
  calc A * (∫ x in Ort N, f x * SpikedWishart.SoftEdge.eigDensity M π x) *
        (∫ x in Ort N, SpikedWishart.SoftEdge.eigDensity M π x)
      = (∫ x in Ort N, f x * SpikedWishart.SoftEdge.eigDensity M π x) *
        (A * ∫ x in Ort N, SpikedWishart.SoftEdge.eigDensity M π x) := by ring
    _ = _ := by rw [← h1, mul_one]

end FC61G
end GlueFC

open SpikedWishart.SoftEdge MeasureTheory in
theorem solution (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j) (hℓ_inj : Function.Injective ℓ)
    (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) (hf_bdd : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hf_sym : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x) :
    ∫ G, f (sampleCov_isHermitian M U ℓ G).eigenvalues ∂(sampleLaw M N) =
      (∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          f lam * eigDensity M (fun j => (ℓ j)⁻¹) lam) /
        ∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          eigDensity M (fun j => (ℓ j)⁻¹) lam := by
  exact FC61G.main M N hN hNM U ℓ hℓ hℓ_inj f hf hf_bdd hf_sym
