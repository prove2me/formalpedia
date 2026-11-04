-- Prove2me | solution 1 for SpikedWishart.SoftEdge.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T23:51:01.639769+00:00
-- url     : https://prove2.me/submissions/8606153d-6e30-4921-ac87-597e561c8e9d

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
/-- S3 algebra: `det (1 - A)` as the alternating sum of principal minors of `A`. -/
theorem det_one_sub_eq_sum_minors {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    (1 - A).det = ∑ k ∈ Finset.range (r + 1), (-1 : ℝ) ^ k *
      ∑ s ∈ (Finset.univ : Finset (Fin r)).powersetCard k,
        (A.submatrix (Subtype.val : s → Fin r) (Subtype.val : s → Fin r)).det := by
  set p : ℝ[X] := (1 + (X : ℝ[X]) • A.map C).det with hp
  have hev : p.eval (-1) = (1 - A).det := by
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply, sub_eq_add_neg]
    split_ifs <;> simp
  have hdeg : p.natDegree < r + 1 := by
    have h := Polynomial.natDegree_det_X_add_C_le A 1
    have he : (X : ℝ[X]) • A.map C + (1 : Matrix (Fin r) (Fin r) ℝ).map C = 1 + (X : ℝ[X]) • A.map C := by
      rw [add_comm, Matrix.map_one _ (map_zero C) (map_one C)]
    rw [he, Fintype.card_fin] at h
    rw [hp]
    omega
  rw [← hev, Polynomial.eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hp, Matrix.coeff_det_one_add_X_smul_eq_sum_minors, mul_comm]



/-- Cauchy-Binet, unsorted form: expand each row of a rank-`r` product by multilinearity. -/
theorem det_sum_mul_expand {R : Type*} [CommRing R] {n r : ℕ} (Φ : Fin n → Fin r → R)
    (Ψ : Fin r → Fin n → R) :
    (Matrix.of fun i j : Fin n => ∑ a, Φ i a * Ψ a j).det =
      ∑ f : Fin n → Fin r, (∏ i, Φ i (f i)) * (Matrix.of fun i j : Fin n => Ψ (f i) j).det := by
  have hrow : (Matrix.of fun i j : Fin n => ∑ a, Φ i a * Ψ a j) =
      fun i => ∑ a ∈ (Finset.univ : Finset (Fin r)), Φ i a • Ψ a := by
    ext i j
    simp [Finset.sum_apply]
  change (Matrix.detRowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R).toMultilinearMap
    (Matrix.of fun i j : Fin n => ∑ a, Φ i a * Ψ a j) = _
  rw [hrow, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- Pointwise: the rank-`r` kernel determinant as a signed sum of coordinate products. -/
theorem det_kernel_pointwise {n r : ℕ} (φ ψ : Fin r → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)).det =
      ∑ f : Fin n → Fin r, ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, (ψ (f (σ j)) (u j) * φ (f j) (u j)) := by
  rw [det_sum_mul_expand (fun i a => φ a (u i)) (fun a j => ψ a (u j))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.of_apply]
  ring

/-- Integrated Cauchy-Binet, unsorted: the `n`-fold integral of a rank-`r` kernel determinant. -/
theorem integral_det_kernel {n r : ℕ} (φ ψ : Fin r → ℝ → ℝ) (x : ℝ)
    (hint : ∀ a b, IntegrableOn (fun u => ψ a u * φ b u) (Set.Ioi x)) :
    ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
        (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)).det =
      ∑ f : Fin n → Fin r,
        ((Matrix.of fun a b : Fin r => ∫ u in Set.Ioi x, ψ a u * φ b u).submatrix f f).det := by
  have hμ : (volume : Measure (Fin n → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin n => Set.Ioi x)) =
      Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioi x)) := by
    rw [MeasureTheory.volume_pi]
    exact Measure.restrict_pi_pi _ _
  have hI : ∀ (f : Fin n → Fin r) (σ : Equiv.Perm (Fin n)),
      Integrable (fun u : Fin n → ℝ => ∏ j, (ψ (f (σ j)) (u j) * φ (f j) (u j)))
        (Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioi x))) :=
    fun f σ => Integrable.fintype_prod (f := fun j t => ψ (f (σ j)) t * φ (f j) t)
      (fun j => hint _ _)
  simp_rw [det_kernel_pointwise φ ψ]
  rw [hμ, integral_finsetSum _ (fun f _ => integrable_finsetSum _ (fun σ _ => (hI f σ).const_mul _))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_finsetSum _ (fun σ _ => (hI f σ).const_mul _), Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun j t => ψ (f (σ j)) t * φ (f j) t)]
  rfl

/-- Sorting step of Cauchy-Binet: only injective index maps survive, each `s` counted `n!` times. -/
theorem sum_submatrix_det_eq {n r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    ∑ f : Fin n → Fin r, (A.submatrix f f).det =
      (n.factorial : ℝ) * ∑ s ∈ (Finset.univ : Finset (Fin r)).powersetCard n,
        (A.submatrix (Subtype.val : s → Fin r) (Subtype.val : s → Fin r)).det := by
  classical
  have h0 : ∀ f : Fin n → Fin r, ¬ Function.Injective f → (A.submatrix f f).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun f _ h => by by_contra hf; exact h (h0 f hf))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f => Finset.univ.image f)
    (t := (Finset.univ : Finset (Fin r)).powersetCard n)]
  swap
  · intro f hf
    have hinj : Function.Injective f := (Finset.mem_filter.1 hf).2
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ hinj]; simp⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsc : s.card = n := (Finset.mem_powersetCard.1 hs).2
  set e : Fin n ≃ s := (s.orderIsoOfFin hsc).toEquiv with he
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (A.submatrix (fun i => ((e (σ i) : s) : Fin r)) (fun i => ((e (σ i) : s) : Fin r))).det =
        (A.submatrix (Subtype.val : s → Fin r) (Subtype.val : s → Fin r)).det := by
    intro σ
    have : A.submatrix (fun i => ((e (σ i) : s) : Fin r)) (fun i => ((e (σ i) : s) : Fin r)) =
        (A.submatrix (Subtype.val : s → Fin r) (Subtype.val : s → Fin r)).submatrix
          (σ.trans e) (σ.trans e) := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
  have hcard : (n.factorial : ℝ) = ((Finset.univ : Finset (Equiv.Perm (Fin n))).card : ℝ) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const]
  symm
  refine Finset.sum_bij (fun σ _ => fun i => ((e (σ i) : s) : Fin r)) ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Subtype.val_injective.comp (e.injective.comp σ.injective), ?_⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e (σ i)).2
    · intro hy
      exact ⟨σ.symm (e.symm ⟨y, hy⟩), by simp⟩
  · intro σ _ τ _ h
    exact Equiv.ext fun i => e.injective (Subtype.ext (congrFun h i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨hinj, him⟩ := hf
    have hmem : ∀ i, f i ∈ s := fun i => him ▸ Finset.mem_image_of_mem f (Finset.mem_univ i)
    let k : Fin n → Fin n := fun i => e.symm ⟨f i, hmem i⟩
    have hk : Function.Injective k := by
      intro i j hij
      apply hinj
      have := congrArg (fun t => ((e t : s) : Fin r)) hij
      simpa [k] using this
    refine ⟨Equiv.ofBijective k (Finite.injective_iff_bijective.1 hk), Finset.mem_univ _, ?_⟩
    funext i
    simp [k]
  · intro σ _
    exact (hterm σ).symm



/-- S3 rank step: a kernel matrix of a rank-`r` kernel is singular once `n > r`. -/
theorem det_finiteRank_eq_zero {r n : ℕ} (hn : r < n) (φ ψ : Fin r → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)).det = 0 := by
  have hfac : (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)) =
      (Matrix.of fun (i : Fin n) (a : Fin r) => φ a (u i)) *
        (Matrix.of fun (a : Fin r) (j : Fin n) => ψ a (u j)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hfac]
  by_contra h
  have hu : IsUnit ((Matrix.of fun (i : Fin n) (a : Fin r) => φ a (u i)) *
        (Matrix.of fun (a : Fin r) (j : Fin n) => ψ a (u j))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_left (Matrix.of fun (i : Fin n) (a : Fin r) => φ a (u i))
    (Matrix.of fun (a : Fin r) (j : Fin n) => ψ a (u j))
  have h3 := Matrix.rank_le_width (Matrix.of fun (i : Fin n) (a : Fin r) => φ a (u i))
  simp only [Fintype.card_fin] at h1 h3
  omega


/-- S3 step 1: a finite-rank Fredholm series is a finite sum (terms `n > r` vanish). -/
theorem fredholmDet_eq_sum_range {r : ℕ} (φ ψ : Fin r → ℝ → ℝ) (K : ℝ → ℝ → ℝ) (x : ℝ)
    (hK : ∀ u v, x < u → x < v → K u v = ∑ a, φ a u * ψ a v) :
    SpikedWishart.SoftEdge.fredholmDet K x =
      ∑ n ∈ Finset.range (r + 1), ((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
        ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
          (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)).det := by
  have hc : ∀ n : ℕ, (∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
      (Matrix.of fun i j : Fin n => K (u i) (u j)).det) =
      ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
        (Matrix.of fun i j : Fin n => ∑ a, φ a (u i) * ψ a (u j)).det := by
    intro n
    refine setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)) ?_
    intro u hu
    refine congrArg Matrix.det ?_
    ext i j
    simp only [Matrix.of_apply]
    exact hK _ _ (hu i (Set.mem_univ i)) (hu j (Set.mem_univ j))
  unfold SpikedWishart.SoftEdge.fredholmDet
  simp_rw [hc]
  refine tsum_eq_sum ?_
  intro n hn
  have hrn : r < n := by simp at hn; omega
  simp [det_finiteRank_eq_zero hrn]

/-- Child C statement as a Prop. -/
def fredholmDet_finiteRank_stmt : Prop :=
  ∀ (r : ℕ) (φ ψ : Fin r → ℝ → ℝ) (K : ℝ → ℝ → ℝ) (x : ℝ),
    (∀ u v, x < u → x < v → K u v = ∑ a, φ a u * ψ a v) →
    (∀ a b, IntegrableOn (fun u => φ a u * ψ b u) (Set.Ioi x)) →
    SpikedWishart.SoftEdge.fredholmDet K x =
      (1 - Matrix.of fun a b : Fin r => ∫ u in Set.Ioi x, ψ a u * φ b u).det


/-- Child C: Fredholm determinant of a finite-rank kernel is a finite determinant. -/
theorem fredholmDet_finiteRank : fredholmDet_finiteRank_stmt := by
  intro r φ ψ K x hK hint
  rw [fredholmDet_eq_sum_range φ ψ K x hK, det_one_sub_eq_sum_minors]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_det_kernel φ ψ x (fun a b => by
    simpa only [mul_comm] using hint b a), sum_submatrix_det_eq]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

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

/-- `(z/w)^M/(w-z) = 1/(w-z) - Σ_{i<M} z^i/w^{i+1}`. -/
theorem geom_split (z w : ℂ) (hw : w ≠ 0) (hwz : w - z ≠ 0) (M : ℕ) :
    (z / w) ^ M / (w - z) = 1 / (w - z) - ∑ i ∈ Finset.range M, z ^ i / w ^ (i + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', pow_succ', mul_div_assoc, ih]
    have e : ∑ i ∈ Finset.range n, z ^ (i + 1) / w ^ (i + 1 + 1) =
        (z / w) * ∑ i ∈ Finset.range n, z ^ i / w ^ (i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', pow_succ' w (i + 1)]
      field_simp
    rw [e]
    field_simp
    ring

/-- Telescoping: `Π(π_j - w) = P(z) - (w - z) Σ_k Π_{j<k}(π_j - w) Π_{j>k}(π_j - z)`. -/
theorem prod_tele {N : ℕ} (π : Fin N → ℝ) (z w : ℂ) :
    ∏ j, ((π j : ℂ) - w) = Pz π z - (w - z) * ∑ k : Fin N,
      (∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w)) *
        ∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z) := by
  have h := Finset.prod_sub_ordered (Finset.univ : Finset (Fin N))
    (fun j => (π j : ℂ) - z) (fun _ => w - z)
  simp only [sub_sub_sub_cancel_right] at h
  rw [h, Pz, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Pointwise splitting of the kernel integrand. -/
theorem integrand_split {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q η ζ : ℝ) (z w : ℂ)
    (hz : Pz π z ≠ 0) (hw : w ≠ 0) (hwz : w - z ≠ 0) :
    exp (-(η : ℂ) * M * (z - q) + (ζ : ℂ) * M * (w - q)) * (1 / (w - z)) * (z / w) ^ M *
        ∏ j, (((π j : ℂ) - w) / ((π j : ℂ) - z)) =
      exp (-(η : ℂ) * M * (z - q)) * (exp ((ζ : ℂ) * M * (w - q)) / (w - z))
      - ∑ i ∈ Finset.range M, (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
          (exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1))
      - ∑ k, Ak M π q η k z * Bk M π q ζ k w := by
  have hAB : ∑ k, Ak M π q η k z * Bk M π q ζ k w =
      exp (-(η : ℂ) * M * (z - q)) * exp ((ζ : ℂ) * M * (w - q)) * (z / w) ^ M *
        ((∑ k : Fin N, (∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w)) *
          ∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z)) / Pz π z) := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Ak, Bk, div_pow]
    ring
  have hgeo : ∑ i ∈ Finset.range M, (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
        (exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1)) =
      exp (-(η : ℂ) * M * (z - q)) * exp ((ζ : ℂ) * M * (w - q)) *
        (1 / (w - z) - (z / w) ^ M / (w - z)) := by
    rw [geom_split z w hw hwz M, sub_sub_cancel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hAB, hgeo, exp_add, Finset.prod_div_distrib, prod_tele π z w,
    show (∏ x, ((π x : ℂ) - z)) = Pz π z from rfl]
  field_simp
  ring

open ComplexConjugate in
/-- A circle integral around a real centre of a conj-symmetric function is purely imaginary. -/
theorem conj_circleIntegral (f : ℂ → ℂ) (c R : ℝ) (hf : ∀ z, f (conj z) = conj (f z)) :
    conj (∮ z in C((c : ℂ), R), f z) = -(∮ z in C((c : ℂ), R), f z) := by
  unfold circleIntegral
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have key : ∀ θ : ℝ, conj (deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ)) =
      -(deriv (circleMap (c : ℂ) R) (-θ) • f (circleMap (c : ℂ) R (-θ))) := by
    intro θ
    simp only [deriv_circleMap, smul_eq_mul, map_mul, conj_I, ← hf,
      conj_circleMap, conj_ofReal, map_zero]
    ring
  rw [intervalIntegral.integral_of_le h2π, ← integral_conj, ← intervalIntegral.integral_of_le h2π]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg
    (fun θ => deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ))]
  congr 1
  have hper : Function.Periodic
      (fun θ => deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ)) (2 * Real.pi) := by
    intro θ
    simp only [deriv_circleMap, periodic_circleMap _ _ θ]
  have := hper.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  simp only [neg_add_cancel, zero_add] at this
  rw [← intervalIntegral.integral_of_le h2π]
  simpa using this

open ComplexConjugate in
theorem real_of_conj (X : ℂ) (hX : conj X = -X) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * X = ((((2 * (Real.pi : ℂ) * I)⁻¹ * X).re : ℝ) : ℂ) := by
  refine (Complex.conj_eq_iff_re.1 ?_).symm
  rw [map_mul, map_inv₀, hX]
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I, mul_neg, inv_neg, neg_mul, neg_neg]

open ComplexConjugate in
theorem Ak_conj {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q η : ℝ) (k : Fin N) (z : ℂ) :
    Ak M π q η k (conj z) = conj (Ak M π q η k z) := by
  simp only [Ak, Pz, map_mul, map_div₀, map_prod, map_sub, map_pow, map_neg, ← exp_conj,
    conj_ofReal, map_natCast]

open ComplexConjugate in
theorem Bk_conj {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q ζ : ℝ) (k : Fin N) (w : ℂ) :
    Bk M π q ζ k (conj w) = conj (Bk M π q ζ k w) := by
  simp only [Bk, map_mul, map_div₀, map_prod, map_sub, map_pow, map_one, ← exp_conj,
    conj_ofReal, map_natCast]

theorem int_mul_const (f : ℂ → ℂ) (a c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z * a) = (∮ z in C(c, R), f z) * a := by
  simpa only [smul_eq_mul] using circleIntegral.integral_smul_const f a c R

theorem re_le_of_mem_closedBall (c R : ℝ) (w : ℂ) (hw : w ∈ Metric.closedBall (c : ℂ) R) :
    w.re ≤ c + R := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h := Complex.abs_re_le_norm (w - c)
  rw [Complex.sub_re, ofReal_re] at h
  linarith [le_abs_self (w.re - c)]

theorem le_re_of_mem_sphere (c R : ℝ) (z : ℂ) (hz : z ∈ Metric.sphere (c : ℂ) R) :
    c - R ≤ z.re := by
  rw [mem_sphere_iff_norm] at hz
  have h := Complex.abs_re_le_norm (z - c)
  rw [hz, Complex.sub_re, ofReal_re] at h
  linarith [neg_abs_le (z.re - c)]

/-- Cauchy: `∮_Σ e^{ζM(w-q)}/(w-z) dw = 0` when `z` lies to the right of the closed disc. -/
theorem cauchy_w (M : ℕ) (q ζ cS ρS : ℝ) (hρS : 0 ≤ ρS) (z : ℂ) (hz : cS + ρS < z.re) :
    (∮ w in C((cS : ℂ), ρS), exp ((ζ : ℂ) * M * (w - q)) / (w - z)) = 0 := by
  have hd : ∀ w ∈ Metric.closedBall (cS : ℂ) ρS,
      DifferentiableAt ℂ (fun w => exp ((ζ : ℂ) * M * (w - q)) / (w - z)) w := by
    intro w hw
    have hne : w - z ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re] at this
      linarith [re_le_of_mem_closedBall cS ρS w hw]
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) hne
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hρS Set.countable_empty
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (Metric.ball_subset_closedBall hw.1))

/-- Cauchy: an entire integrand has zero circle integral. -/
theorem cauchy_entire (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∮ z in C(c, R), f z) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hR Set.countable_empty
    hf.continuous.continuousOn (fun z _ => hf z)

theorem Ak_contOn {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q η : ℝ) (k : Fin N) (c R : ℝ)
    (hP : ∀ z ∈ Metric.sphere (c : ℂ) R, Pz π z ≠ 0) :
    ContinuousOn (Ak M π q η k) (Metric.sphere (c : ℂ) R) := by
  unfold Ak
  exact ContinuousOn.div (by fun_prop) (by unfold Pz; fun_prop) hP

theorem Bk_contOn {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q ζ : ℝ) (k : Fin N) (c R : ℝ)
    (h0 : ∀ w ∈ Metric.sphere (c : ℂ) R, w ≠ 0) :
    ContinuousOn (Bk M π q ζ k) (Metric.sphere (c : ℂ) R) := by
  unfold Bk
  refine ContinuousOn.mul (ContinuousOn.mul (by fun_prop) ?_) (by fun_prop)
  exact ContinuousOn.div continuousOn_const (by fun_prop) fun w hw => pow_ne_zero _ (h0 w hw)

/-- The inner (w) integral of the kernel integrand, for `z` to the right of `Σ`. -/
theorem inner_w {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q η ζ cS ρS : ℝ) (hρS : 0 ≤ ρS)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (z : ℂ) (hz : cS + ρS < z.re)
    (hPz : Pz π z ≠ 0) :
    (∮ w in C((cS : ℂ), ρS), exp (-(η : ℂ) * M * (z - q) + (ζ : ℂ) * M * (w - q)) *
        (1 / (w - z)) * (z / w) ^ M * ∏ j, (((π j : ℂ) - w) / ((π j : ℂ) - z))) =
      -(∑ i ∈ Finset.range M, (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
          ∮ w in C((cS : ℂ), ρS), exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1))
      - ∑ k, Ak M π q η k z * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w := by
  have hwz : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w - z ≠ 0 := by
    intro w hw h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at this
    linarith [re_le_of_mem_closedBall cS ρS w (Metric.sphere_subset_closedBall hw)]
  rw [circleIntegral.integral_congr hρS
    (fun w hw => integrand_split M π q η ζ z w hPz (h0 w hw) (hwz w hw))]
  have k1 : ContinuousOn (fun w => exp (-(η : ℂ) * M * (z - q)) *
      (exp ((ζ : ℂ) * M * (w - q)) / (w - z))) (Metric.sphere (cS : ℂ) ρS) :=
    ContinuousOn.mul continuousOn_const (ContinuousOn.div (by fun_prop) (by fun_prop) hwz)
  have k2i : ∀ i : ℕ, ContinuousOn (fun w => exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1))
      (Metric.sphere (cS : ℂ) ρS) := fun i =>
    ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => pow_ne_zero _ (h0 w hw)
  have k2 : ContinuousOn (fun w => ∑ i ∈ Finset.range M, (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
      (exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1))) (Metric.sphere (cS : ℂ) ρS) :=
    continuousOn_finsetSum _ fun i _ => ContinuousOn.mul continuousOn_const (k2i i)
  have k3 : ContinuousOn (fun w => ∑ k, Ak M π q η k z * Bk M π q ζ k w)
      (Metric.sphere (cS : ℂ) ρS) :=
    continuousOn_finsetSum _ fun k _ =>
      ContinuousOn.mul continuousOn_const (Bk_contOn M π q ζ k cS ρS h0)
  have k12 : ContinuousOn (fun w => exp (-(η : ℂ) * M * (z - q)) *
      (exp ((ζ : ℂ) * M * (w - q)) / (w - z)) - ∑ i ∈ Finset.range M,
        (exp (-(η : ℂ) * M * (z - q)) * z ^ i) * (exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1)))
      (Metric.sphere (cS : ℂ) ρS) := k1.sub k2
  rw [circleIntegral.integral_sub (k12.circleIntegrable hρS) (k3.circleIntegrable hρS),
    circleIntegral.integral_sub (k1.circleIntegrable hρS) (k2.circleIntegrable hρS),
    circleIntegral.integral_const_mul, cauchy_w M q ζ cS ρS hρS z hz,
    circleIntegral.integral_fun_sum (f := fun i w => (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
        (exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1)))
      (fun i _ => (ContinuousOn.mul continuousOn_const (k2i i)).circleIntegrable hρS),
    circleIntegral.integral_fun_sum (f := fun k w => Ak M π q η k z * Bk M π q ζ k w)
      (fun k _ => (ContinuousOn.mul continuousOn_const
        (Bk_contOn M π q ζ k cS ρS h0)).circleIntegrable hρS)]
  simp only [circleIntegral.integral_const_mul, mul_zero, zero_sub]

/-- The kernel as a finite sum of products of circle integrals. -/
theorem kernel_split {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ) (hρΓ : 0 ≤ ρΓ)
    (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (η ζ : ℝ) :
    SpikedWishart.SoftEdge.kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      ((M : ℂ) / (2 * (Real.pi : ℂ) * I) ^ 2 *
        -(∑ k, (∮ z in C((cΓ : ℂ), ρΓ), Ak M π q η k z) *
          ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w)).re := by
  unfold SpikedWishart.SoftEdge.kernelKMN
  congr 2
  rw [circleIntegral.integral_congr hρΓ (fun z hz => inner_w M π q η ζ cS ρS hρS h0 z
    (by linarith [le_re_of_mem_sphere cΓ ρΓ z hz]) (hP z hz))]
  have hd : Differentiable ℂ (fun z => -(∑ i ∈ Finset.range M,
      (exp (-(η : ℂ) * M * (z - q)) * z ^ i) *
        ∮ w in C((cS : ℂ), ρS), exp ((ζ : ℂ) * M * (w - q)) / w ^ (i + 1))) := by
    fun_prop
  have kA : ContinuousOn (fun z => ∑ k, Ak M π q η k z * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w)
      (Metric.sphere (cΓ : ℂ) ρΓ) :=
    continuousOn_finsetSum _ fun k _ =>
      ContinuousOn.mul (Ak_contOn M π q η k cΓ ρΓ hP) continuousOn_const
  rw [circleIntegral.integral_sub (hd.continuous.continuousOn.circleIntegrable hρΓ)
      (kA.circleIntegrable hρΓ), cauchy_entire _ hd _ _ hρΓ,
    circleIntegral.integral_fun_sum
      (f := fun k z => Ak M π q η k z * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w)
      (fun k _ => (ContinuousOn.mul (Ak_contOn M π q η k cΓ ρΓ hP)
        continuousOn_const).circleIntegrable hρΓ)]
  simp only [int_mul_const, zero_sub]

/-- Real z-side functions `α_k(η) = (2πi)⁻¹ ∮_Γ A_k`. -/
noncomputable def alpha {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ : ℝ) (k : Fin N) (η : ℝ) : ℝ :=
  ((2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ), Ak M π q η k z).re

/-- Real w-side functions `β_k(ζ) = (2πi)⁻¹ ∮_Σ B_k`. -/
noncomputable def beta {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cS ρS : ℝ) (k : Fin N) (ζ : ℝ) : ℝ :=
  ((2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w).re

theorem circ_eq_alpha {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ : ℝ) (k : Fin N) (η : ℝ) :
    (∮ z in C((cΓ : ℂ), ρΓ), Ak M π q η k z) =
      2 * (Real.pi : ℂ) * I * (alpha M π q cΓ ρΓ k η : ℂ) := by
  rw [alpha, ← real_of_conj _ (conj_circleIntegral _ cΓ ρΓ (Ak_conj M π q η k)),
    ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]

theorem circ_eq_beta {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cS ρS : ℝ) (k : Fin N) (ζ : ℝ) :
    (∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w) =
      2 * (Real.pi : ℂ) * I * (beta M π q cS ρS k ζ : ℂ) := by
  rw [beta, ← real_of_conj _ (conj_circleIntegral _ cS ρS (Bk_conj M π q ζ k)),
    ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]

/-- CHILD B: the kernel `K_{M,N}` has rank `≤ N`, for any `π` (coinciding values allowed). -/
theorem kernelKMN_finiteRank {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ) (hρΓ : 0 ≤ ρΓ)
    (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (η ζ : ℝ) :
    SpikedWishart.SoftEdge.kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      ∑ k, (-(M : ℝ) * alpha M π q cΓ ρΓ k η) * beta M π q cS ρS k ζ := by
  rw [kernel_split M π q cΓ ρΓ cS ρS hρΓ hρS hsep hP h0 η ζ]
  simp only [circ_eq_alpha, circ_eq_beta]
  have e : (M : ℂ) / (2 * (Real.pi : ℂ) * I) ^ 2 *
      -(∑ k, 2 * (Real.pi : ℂ) * I * (alpha M π q cΓ ρΓ k η : ℂ) *
        (2 * (Real.pi : ℂ) * I * (beta M π q cS ρS k ζ : ℂ))) =
      ((∑ k, (-(M : ℝ) * alpha M π q cΓ ρΓ k η) * beta M π q cS ρS k ζ : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 := two_pi_I_ne_zero
    field_simp
  rw [e, ofReal_re]

theorem circle_param_cont (F E : ℝ → ℂ → ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hg : ContinuousOn g (Metric.sphere c R)) (hE : Continuous (Function.uncurry E))
    (hFE : ∀ u : ℝ, ∀ z ∈ Metric.sphere c R, F u z = E u z * g z) :
    Continuous (fun u : ℝ => ∮ z in C(c, R), F u z) := by
  have e : (fun u : ℝ => ∮ z in C(c, R), F u z) = fun u => ∮ z in C(c, R), E u z * g z :=
    funext fun u => circleIntegral.integral_congr hR (fun z hz => hFE u z hz)
  rw [e]
  have hgc : Continuous (fun φ : ℝ => g (circleMap c R φ)) :=
    hg.comp_continuous (continuous_circleMap c R) (fun φ => circleMap_mem_sphere c hR φ)
  unfold circleIntegral
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * Real.pi)
  have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap c R) p.2 := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have h3 : Continuous fun p : ℝ × ℝ => E p.1 (circleMap c R p.2) :=
    hE.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
  exact h1.smul (h3.mul (hgc.comp continuous_snd))

theorem alpha_continuous {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ : ℝ) (hρΓ : 0 ≤ ρΓ)
    (hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0) (k : Fin N) :
    Continuous (alpha M π q cΓ ρΓ k) := by
  have hc := circle_param_cont (fun η z => Ak M π q η k z)
    (fun η z => exp (-(η : ℂ) * M * (z - q)))
    (fun z => z ^ M * (∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z)) / Pz π z)
    (cΓ : ℂ) ρΓ hρΓ (ContinuousOn.div (by fun_prop) (by unfold Pz; fun_prop) hP)
    (by fun_prop) (fun η z _ => by unfold Ak; ring)
  exact (Complex.continuous_re.comp (continuous_const.mul hc))

theorem beta_continuous {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cS ρS : ℝ) (hρS : 0 ≤ ρS)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (k : Fin N) :
    Continuous (beta M π q cS ρS k) := by
  have hc := circle_param_cont (fun ζ w => Bk M π q ζ k w)
    (fun ζ w => exp ((ζ : ℂ) * M * (w - q)))
    (fun w => (1 / w ^ M) * ∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w))
    (cS : ℂ) ρS hρS (ContinuousOn.mul (ContinuousOn.div continuousOn_const (by fun_prop)
      fun w hw => pow_ne_zero _ (h0 w hw)) (by fun_prop))
    (by fun_prop) (fun ζ w _ => by unfold Bk; ring)
  exact (Complex.continuous_re.comp (continuous_const.mul hc))

theorem alpha_bound {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ : ℝ) (hρΓ : 0 ≤ ρΓ)
    (hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0) (k : Fin N) :
    ∃ C : ℝ, ∀ η : ℝ, 0 ≤ η →
      |alpha M π q cΓ ρΓ k η| ≤ C * Real.exp (-(η * M * (cΓ - ρΓ - q))) := by
  obtain ⟨C0, hC0⟩ := (isCompact_sphere (cΓ : ℂ) ρΓ).exists_bound_of_continuousOn
    (ContinuousOn.div (f := fun z => z ^ M *
      (∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z))) (by fun_prop)
      (by unfold Pz; fun_prop) hP)
  refine ⟨ρΓ * C0, fun η hη => ?_⟩
  have hb : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ,
      ‖Ak M π q η k z‖ ≤ Real.exp (-(η * M * (cΓ - ρΓ - q))) * C0 := by
    intro z hz
    have e : Ak M π q η k z = exp (-(η : ℂ) * M * (z - q)) *
        (z ^ M * (∏ j ∈ Finset.univ.filter (fun j => k < j), ((π j : ℂ) - z)) / Pz π z) := by
      unfold Ak; ring
    rw [e, norm_mul, norm_exp]
    refine mul_le_mul ?_ (hC0 z hz) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    have hre : (-(η : ℂ) * M * (z - q)).re = -(η * M * (z.re - q)) := by simp
    rw [hre]
    have := le_re_of_mem_sphere cΓ ρΓ z hz
    have hηM : 0 ≤ η * M := mul_nonneg hη (Nat.cast_nonneg M)
    nlinarith
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρΓ hb
  rw [smul_eq_mul] at h
  calc |alpha M π q cΓ ρΓ k η| ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ), Ak M π q η k z‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ρΓ * (Real.exp (-(η * M * (cΓ - ρΓ - q))) * C0) := h
    _ = ρΓ * C0 * Real.exp (-(η * M * (cΓ - ρΓ - q))) := by ring

theorem beta_bound {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cS ρS : ℝ) (hρS : 0 ≤ ρS)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (k : Fin N) :
    ∃ C : ℝ, ∀ ζ : ℝ, 0 ≤ ζ →
      |beta M π q cS ρS k ζ| ≤ C * Real.exp (ζ * M * (cS + ρS - q)) := by
  obtain ⟨C0, hC0⟩ := (isCompact_sphere (cS : ℂ) ρS).exists_bound_of_continuousOn
    (ContinuousOn.mul (ContinuousOn.div continuousOn_const (by fun_prop)
      fun w hw => pow_ne_zero M (h0 w hw))
      (by fun_prop : ContinuousOn (fun w : ℂ =>
        ∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w)) _))
  refine ⟨ρS * C0, fun ζ hζ => ?_⟩
  have hb : ∀ w ∈ Metric.sphere (cS : ℂ) ρS,
      ‖Bk M π q ζ k w‖ ≤ Real.exp (ζ * M * (cS + ρS - q)) * C0 := by
    intro w hw
    have e : Bk M π q ζ k w = exp ((ζ : ℂ) * M * (w - q)) *
        ((1 / w ^ M) * ∏ j ∈ Finset.univ.filter (fun j => j < k), ((π j : ℂ) - w)) := by
      unfold Bk; ring
    rw [e, norm_mul, norm_exp]
    refine mul_le_mul ?_ (hC0 w hw) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    have hre : ((ζ : ℂ) * M * (w - q)).re = ζ * M * (w.re - q) := by simp
    rw [hre]
    have := re_le_of_mem_closedBall cS ρS w (Metric.sphere_subset_closedBall hw)
    have hζM : 0 ≤ ζ * M := mul_nonneg hζ (Nat.cast_nonneg M)
    nlinarith
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρS hb
  rw [smul_eq_mul] at h
  calc |beta M π q cS ρS k ζ| ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), Bk M π q ζ k w‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ρS * (Real.exp (ζ * M * (cS + ρS - q)) * C0) := h
    _ = ρS * C0 * Real.exp (ζ * M * (cS + ρS - q)) := by ring

/-- Integrability of the products `φ_a ψ_b` on `(x, ∞)`, `x ≥ 0`, needed by child C. -/
theorem integrableOn_phi_psi {N : ℕ} (M : ℕ) (hM : 0 < M) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0)
    (h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0) (x : ℝ) (hx : 0 ≤ x) (a b : Fin N) :
    MeasureTheory.IntegrableOn (fun u => (-(M : ℝ) * alpha M π q cΓ ρΓ a u) *
      beta M π q cS ρS b u) (Set.Ioi x) := by
  obtain ⟨Ca, hCa⟩ := alpha_bound M π q cΓ ρΓ hρΓ hP a
  obtain ⟨Cb, hCb⟩ := beta_bound M π q cS ρS hρS h0 b
  have hδ : 0 < (M : ℝ) * ((cΓ - ρΓ) - (cS + ρS)) :=
    mul_pos (Nat.cast_pos.2 hM) (by linarith)
  have hg := (exp_neg_integrableOn_Ioi x hδ).const_mul ((M : ℝ) * |Ca| * |Cb|)
  refine hg.mono' ?_ ?_
  · exact ((continuous_const.mul (alpha_continuous M π q cΓ ρΓ hρΓ hP a)).mul
      (beta_continuous M π q cS ρS hρS h0 b)).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro u hu
    have hu0 : 0 ≤ u := le_trans hx (le_of_lt hu)
    have ha := hCa u hu0
    have hb := hCb u hu0
    have he : Real.exp (-(u * M * (cΓ - ρΓ - q))) * Real.exp (u * M * (cS + ρS - q)) =
        Real.exp (-((M : ℝ) * ((cΓ - ρΓ) - (cS + ρS))) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, Nat.abs_cast]
    have hCa' : |alpha M π q cΓ ρΓ a u| ≤ |Ca| * Real.exp (-(u * M * (cΓ - ρΓ - q))) :=
      ha.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    have hCb' : |beta M π q cS ρS b u| ≤ |Cb| * Real.exp (u * M * (cS + ρS - q)) :=
      hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    calc (M : ℝ) * |alpha M π q cΓ ρΓ a u| * |beta M π q cS ρS b u|
        ≤ (M : ℝ) * (|Ca| * Real.exp (-(u * M * (cΓ - ρΓ - q)))) *
            (|Cb| * Real.exp (u * M * (cS + ρS - q))) := by
          gcongr
      _ = (M : ℝ) * |Ca| * |Cb| * Real.exp (-((M : ℝ) * ((cΓ - ρΓ) - (cS + ρS))) * u) := by
          rw [← he]; ring

end B4196B
end

section
open MeasureTheory Complex Metric

namespace B4196D

/-- Fubini: swap `∫_{u>0}` with a circle integral, under a uniform exponential bound. -/
theorem swap_circle_Ioi (F : ℝ → ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (ε C : ℝ) (hε : 0 < ε)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ sphere c R))
    (hB : ∀ u : ℝ, 0 ≤ u → ∀ z ∈ sphere c R, ‖F u z‖ ≤ C * Real.exp (-ε * u)) :
    ∫ u in Set.Ioi (0 : ℝ), (∮ z in C(c, R), F u z) =
      ∮ z in C(c, R), ∫ u in Set.Ioi (0 : ℝ), F u z := by
  simp only [circleIntegral_def_Icc]
  have hsm : ∀ θ : ℝ, (∫ u in Set.Ioi (0 : ℝ), deriv (circleMap c R) θ • F u (circleMap c R θ)) =
      deriv (circleMap c R) θ • ∫ u in Set.Ioi (0 : ℝ), F u (circleMap c R θ) :=
    fun θ => integral_smul _ _
  simp_rw [← hsm]
  refine integral_integral_swap ?_
  have hcont : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2 • F p.1 (circleMap c R p.2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => F p.1 (circleMap c R p.2)) := by
      have := hF.comp_continuous (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
        (fun p => ⟨Set.mem_univ _, circleMap_mem_sphere c hR p.2⟩)
      exact this
    have h2 : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2) := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    exact h2.smul h1
  have hg : Integrable (fun p : ℝ × ℝ => (R * C * Real.exp (-ε * p.1)) * (1 : ℝ))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc 0 (2 * Real.pi)))) := by
    refine Integrable.mul_prod (f := fun u : ℝ => R * C * Real.exp (-ε * u)) (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_
    · have := (exp_neg_integrableOn_Ioi 0 hε).const_mul (R * C)
      refine this.congr ?_
      refine Filter.Eventually.of_forall (fun u => ?_)
      simp only [neg_mul]
    · exact (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).integrableOn_Icc
  refine hg.mono' hcont.aestronglyMeasurable ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Icc)]
  refine Filter.Eventually.of_forall (fun p hp => ?_)
  have hu : 0 ≤ p.1 := le_of_lt hp.1
  simp only [Function.uncurry_def, norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I,
    mul_one, abs_of_nonneg hR]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB p.1 hu _ (circleMap_mem_sphere c hR p.2)) hR

/-- `∮ (∏_{j∈S} (p_j - z))⁻¹ = 0` when `|S| ≥ 2` and all `p_j` lie inside the circle. -/
theorem circle_inv_prod_eq_zero {ι : Type*} (S : Finset ι) (hS : 2 ≤ S.card) (p : ι → ℂ) (c : ℂ)
    (r : ℝ) (hp : ∀ j ∈ S, p j ∈ ball c r) :
    (∮ z in C(c, r), (∏ j ∈ S, (p j - z))⁻¹) = 0 := by
  obtain ⟨j0, hj0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (hp j0 hj0)
  have hne : ∀ z, z ∉ ball c r → ∏ j ∈ S, (p j - z) ≠ 0 := by
    intro z hz
    rw [Finset.prod_ne_zero_iff]
    intro j hj h
    rw [sub_eq_zero] at h
    exact hz (h ▸ hp j hj)
  have hann : ∀ R, r ≤ R → (∮ z in C(c, R), (∏ j ∈ S, (p j - z))⁻¹) =
      ∮ z in C(c, r), (∏ j ∈ S, (p j - z))⁻¹ := by
    intro R hR
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hR Set.countable_empty ?_ ?_
    · exact ContinuousOn.inv₀ (by fun_prop) (fun z hz => hne z hz.2)
    · intro z hz
      refine DifferentiableAt.inv (by fun_prop) (hne z ?_)
      intro hb
      exact hz.1.2 (ball_subset_closedBall hb)
  set I := ∮ z in C(c, r), (∏ j ∈ S, (p j - z))⁻¹
  have hbound : ∀ R, 2 * r ≤ R → 2 ≤ R → ‖I‖ * R ≤ 8 * Real.pi := by
    intro R h2r h2
    have hRpos : 0 < R := by linarith
    have hb : ∀ z ∈ sphere c R, ‖(∏ j ∈ S, (p j - z))⁻¹‖ ≤ ((R / 2)⁻¹) ^ 2 := by
      intro z hz
      rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
      have hfac : ∀ j ∈ S, ‖p j - z‖⁻¹ ≤ (R / 2)⁻¹ := by
        intro j hj
        have hpj : ‖p j - c‖ < r := by rw [← dist_eq_norm]; exact hp j hj
        have hz' : ‖z - c‖ = R := by rw [← dist_eq_norm]; exact hz
        have : R / 2 ≤ ‖p j - z‖ := by
          have := norm_sub_norm_le (z - c) (p j - c)
          have e : z - c - (p j - c) = -(p j - z) := by ring
          rw [e, norm_neg] at this
          linarith
        exact inv_anti₀ (by linarith) this
      calc ∏ j ∈ S, ‖p j - z‖⁻¹ ≤ ∏ _j ∈ S, (R / 2)⁻¹ :=
            Finset.prod_le_prod (fun j _ => inv_nonneg.2 (norm_nonneg _)) hfac
        _ = ((R / 2)⁻¹) ^ S.card := Finset.prod_const _
        _ ≤ ((R / 2)⁻¹) ^ 2 := by
            refine pow_le_pow_of_le_one (inv_nonneg.2 (by linarith)) ?_ hS
            rw [inv_le_one₀ (by linarith)]; linarith
    have h := circleIntegral.norm_integral_le_of_norm_le_const hRpos.le hb
    rw [hann R (by linarith)] at h
    have e : 2 * Real.pi * R * ((R / 2)⁻¹) ^ 2 = 8 * Real.pi / R := by
      field_simp; ring
    rw [e, le_div_iff₀ hRpos] at h
    exact h
  by_contra hI
  have hpos : 0 < ‖I‖ := norm_pos_iff.2 hI
  have hR0 : 0 ≤ 2 * r + 2 := by linarith
  have h8 : 0 ≤ 8 * Real.pi / ‖I‖ := div_nonneg (by positivity) hpos.le
  have h := hbound (2 * r + 2 + 8 * Real.pi / ‖I‖) (by linarith) (by linarith)
  have e : ‖I‖ * (2 * r + 2 + 8 * Real.pi / ‖I‖) = ‖I‖ * (2 * r + 2) + 8 * Real.pi := by
    field_simp
  rw [e] at h
  have : 0 < ‖I‖ * (2 * r + 2) := mul_pos hpos (by linarith)
  linarith

theorem circ_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
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

theorem geom_split (z w : ℂ) (hw : w ≠ 0) (hwz : w - z ≠ 0) (M : ℕ) :
    (z / w) ^ M / (w - z) = 1 / (w - z) - ∑ i ∈ Finset.range M, z ^ i / w ^ (i + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', pow_succ', mul_div_assoc, ih]
    have e : ∑ i ∈ Finset.range n, z ^ (i + 1) / w ^ (i + 1 + 1) =
        (z / w) * ∑ i ∈ Finset.range n, z ^ i / w ^ (i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', pow_succ' w (i + 1)]
      field_simp
    rw [e]
    field_simp
    ring

/-- Monomial residue: `∮ 1/(w^m (z - w)) = 2πi z^{-m}` for `0` inside and `z` outside. -/
theorem circ_inv_pow_div (m : ℕ) (c : ℂ) (r : ℝ) (h0 : (0 : ℂ) ∈ ball c r) (z : ℂ)
    (hz : z ∉ closedBall c r) :
    (∮ w in C(c, r), 1 / w ^ m / (z - w)) =
      if m = 0 then 0 else 2 * Real.pi * I * (1 / z ^ m) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h0
  have hz0 : z ≠ 0 := fun h => hz (h ▸ ball_subset_closedBall h0)
  have hw0 : ∀ w ∈ sphere c r, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at h0; linarith
  have hwz : ∀ w ∈ sphere c r, w - z ≠ 0 := by
    intro w hw h; rw [sub_eq_zero] at h; exact hz (h ▸ sphere_subset_closedBall hw)
  have hzcl : ∮ w in C(c, r), (w - z)⁻¹ = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty ?_ ?_
    · exact ContinuousOn.inv₀ (by fun_prop) (fun w hw h => hz (sub_eq_zero.1 h ▸ hw))
    · intro w hw
      exact DifferentiableAt.inv (by fun_prop)
        (fun h => hz (sub_eq_zero.1 h ▸ ball_subset_closedBall hw.1))
  have key : ∀ w ∈ sphere c r, 1 / w ^ m / (z - w) =
      (1 / z ^ m) * (∑ i ∈ Finset.range m, z ^ i * (w - 0) ^ (-((i : ℤ) + 1)) - (w - z)⁻¹) := by
    intro w hw
    have hw' := hw0 w hw
    have hwz' := hwz w hw
    have hzw : z - w ≠ 0 := fun h => hwz' (by rw [← neg_sub, h, neg_zero])
    have e1 : ∀ i : ℕ, z ^ i * (w - 0) ^ (-((i : ℤ) + 1)) = z ^ i / w ^ (i + 1) := by
      intro i
      rw [sub_zero, div_eq_mul_inv, zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast]
    simp only [e1]
    have hs : ∑ i ∈ Finset.range m, z ^ i / w ^ (i + 1) = 1 / (w - z) - (z / w) ^ m / (w - z) := by
      rw [geom_split z w hw' hwz' m]; ring
    rw [hs, div_pow]
    field_simp
    ring
  have hint : ∀ i ∈ Finset.range m,
      CircleIntegrable (fun w => z ^ i * (w - 0) ^ (-((i : ℤ) + 1))) c r := by
    intro i _
    refine ContinuousOn.circleIntegrable hr.le ?_
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      (fun w hw => Or.inl (by simpa using hw0 w hw)))
  have hsumI : CircleIntegrable (fun w => ∑ i ∈ Finset.range m, z ^ i * (w - 0) ^ (-((i : ℤ) + 1))) c r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      (fun w hw => Or.inl (by simpa using hw0 w hw)))
  have hinvI : CircleIntegrable (fun w => (w - z)⁻¹) c r :=
    ContinuousOn.circleIntegrable hr.le (ContinuousOn.inv₀ (by fun_prop) hwz)
  rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hsumI hinvI, circ_finset_sum _ _ _ _ hint, hzcl, sub_zero]
  simp_rw [circleIntegral.integral_const_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [if_neg (by omega), Finset.sum_eq_single 0]
    · simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, Int.reduceNeg, zpow_neg_one]
      rw [circleIntegral.integral_sub_inv_of_mem_ball h0]; ring
    · intro i _ hi
      rw [circleIntegral.integral_sub_zpow_of_ne (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hm) h

/-- Polynomial residue: `∮ p(w)/(w^M (z - w)) = 2πi p(z)/z^M` when `deg p < M`. -/
theorem circ_poly_div (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree < M) (c : ℂ) (r : ℝ)
    (h0 : (0 : ℂ) ∈ ball c r) (z : ℂ) (hz : z ∉ closedBall c r) :
    (∮ w in C(c, r), p.eval w / w ^ M / (z - w)) = 2 * Real.pi * I * (p.eval z / z ^ M) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h0
  have hz0 : z ≠ 0 := fun h => hz (h ▸ ball_subset_closedBall h0)
  have hw0 : ∀ w ∈ sphere c r, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at h0; linarith
  have hzw : ∀ w ∈ sphere c r, z - w ≠ 0 := by
    intro w hw h; rw [sub_eq_zero] at h; exact hz (h ▸ sphere_subset_closedBall hw)
  have hpow : ∀ x : ℂ, x ≠ 0 → ∀ i ∈ Finset.range M, x ^ i / x ^ M = 1 / x ^ (M - i) := by
    intro x hx i hi
    rw [Finset.mem_range] at hi
    rw [← pow_sub_mul_pow x hi.le]
    field_simp
  have key : ∀ w ∈ sphere c r, p.eval w / w ^ M / (z - w) =
      ∑ i ∈ Finset.range M, p.coeff i * (1 / w ^ (M - i) / (z - w)) := by
    intro w hw
    rw [Polynomial.eval_eq_sum_range' hp, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mul_div_assoc, mul_div_assoc, hpow w (hw0 w hw) i hi]
  have hint : ∀ i ∈ Finset.range M,
      CircleIntegrable (fun w => p.coeff i * (1 / w ^ (M - i) / (z - w))) c r := by
    intro i _
    refine ContinuousOn.circleIntegrable hr.le ?_
    refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.div continuousOn_const
      (by fun_prop) (fun w hw => pow_ne_zero _ (hw0 w hw))) (by fun_prop) hzw)
  rw [circleIntegral.integral_congr hr.le key, circ_finset_sum _ _ _ _ hint,
    Polynomial.eval_eq_sum_range' hp, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [circleIntegral.integral_const_mul, circ_inv_pow_div _ c r h0 z hz,
    if_neg (by rw [Finset.mem_range] at hi; omega), mul_div_assoc, hpow z hz0 i hi]
  ring

end B4196D

end

section
open MeasureTheory Complex Metric

namespace B4196D
open B4196B

noncomputable def Pa {N : ℕ} (π : Fin N → ℝ) (a : Fin N) : Polynomial ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j => j < a), (Polynomial.C (π j : ℂ) - Polynomial.X)

theorem Pa_eval {N : ℕ} (π : Fin N → ℝ) (a : Fin N) (w : ℂ) :
    (Pa π a).eval w = ∏ j ∈ Finset.univ.filter (fun j => j < a), ((π j : ℂ) - w) := by
  simp [Pa, Polynomial.eval_prod]

theorem Pa_natDegree {N : ℕ} (M : ℕ) (hNM : N ≤ M) (π : Fin N → ℝ) (a : Fin N) :
    (Pa π a).natDegree < M := by
  have hss : Finset.univ.filter (fun j : Fin N => j < a) ⊂ Finset.univ :=
    Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl a⟩
  have hc := Finset.card_lt_card hss
  rw [Finset.card_univ, Fintype.card_fin] at hc
  calc (Pa π a).natDegree
      ≤ ∑ j ∈ Finset.univ.filter (fun j => j < a),
          (Polynomial.C (π j : ℂ) - Polynomial.X).natDegree :=
        by unfold Pa; exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j < a), 1 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = (Finset.univ.filter (fun j : Fin N => j < a)).card := by simp
    _ < M := by omega

theorem Pz_ne_of_ball {N : ℕ} (π : Fin N → ℝ) (cΓ ρΓ : ℝ)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (cΓ : ℂ) ρΓ) :
    ∀ z ∈ sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0 := by
  intro z hz
  unfold Pz
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  rw [sub_eq_zero] at h
  have := hπ j
  rw [h, mem_ball] at this
  rw [mem_sphere] at hz
  linarith

/-- Laplace transform of `β_a`: `∫_0^∞ β_a(u) e^{-uM(z-q)} du = p_a(z) / (M z^M)` for `z` right of `Σ`. -/
theorem beta_laplace {N : ℕ} (M : ℕ) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (q cS ρS : ℝ)
    (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS) (a : Fin N) (z : ℂ) (hz : cS + ρS < z.re) :
    ∫ u in Set.Ioi (0 : ℝ), (beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q)) =
      (Pa π a).eval z / z ^ M / M := by
  have hρS : 0 < ρS := lt_of_le_of_lt dist_nonneg hS0
  have h0 : ∀ w ∈ sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at hS0; linarith
  have hzout : z ∉ closedBall (cS : ℂ) ρS := fun h => by
    have := re_le_of_mem_closedBall cS ρS z h; linarith
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set K : ℂ → ℂ := fun w => 1 / w ^ M * ∏ j ∈ Finset.univ.filter (fun j => j < a), ((π j : ℂ) - w)
    with hK
  have hKc : ContinuousOn K (sphere (cS : ℂ) ρS) :=
    ContinuousOn.mul (ContinuousOn.div continuousOn_const (by fun_prop)
      fun w hw => pow_ne_zero M (h0 w hw)) (by fun_prop)
  obtain ⟨C0, hC0⟩ := (isCompact_sphere (cS : ℂ) ρS).exists_bound_of_continuousOn hKc
  have hb : ∀ u : ℝ, (beta M π q cS ρS a u : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), Bk M π q u a w := by
    intro u; rw [circ_eq_beta, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have eB : ∀ (u : ℝ) (w : ℂ), Bk M π q u a w * exp (-(u : ℂ) * M * (z - q)) =
      exp (((M : ℂ) * (w - z)) * u) * K w := by
    intro u w
    simp only [hK, Bk]
    rw [show ((M : ℂ) * (w - z)) * u = (u : ℂ) * M * (w - q) + (-(u : ℂ) * M * (z - q)) by ring,
      exp_add]
    ring
  have step1 : ∀ u : ℝ, (beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), exp (((M : ℂ) * (w - z)) * u) * K w := by
    intro u
    rw [hb]
    simp only [← eB]
    rw [int_mul_const]
    ring
  simp_rw [step1]
  rw [MeasureTheory.integral_const_mul]
  have hε : 0 < (M : ℝ) * (z.re - (cS + ρS)) := mul_pos (Nat.cast_pos.2 hM) (by linarith)
  have hcont : ContinuousOn (Function.uncurry fun (u : ℝ) (w : ℂ) => exp (((M : ℂ) * (w - z)) * u) * K w)
      (Set.univ ×ˢ sphere (cS : ℂ) ρS) := by
    show ContinuousOn (fun p : ℝ × ℂ => exp (((M : ℂ) * (p.2 - z)) * (p.1 : ℂ)) * K p.2) _
    exact ContinuousOn.mul ((by fun_prop : Continuous fun p : ℝ × ℂ =>
      exp (((M : ℂ) * (p.2 - z)) * (p.1 : ℂ))).continuousOn)
      (hKc.comp continuousOn_snd (fun p hp => hp.2))
  have hbd : ∀ u : ℝ, 0 ≤ u → ∀ w ∈ sphere (cS : ℂ) ρS,
      ‖exp (((M : ℂ) * (w - z)) * u) * K w‖ ≤ C0 * Real.exp (-((M : ℝ) * (z.re - (cS + ρS))) * u) := by
    intro u hu w hw
    rw [norm_mul, norm_exp, mul_comm C0]
    refine mul_le_mul ?_ (hC0 w hw) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    have hre : (((M : ℂ) * (w - z)) * u).re = M * (w.re - z.re) * u := by simp <;> ring
    rw [hre]
    have := re_le_of_mem_closedBall cS ρS w (sphere_subset_closedBall hw)
    have hMu : 0 ≤ (M : ℝ) * u := mul_nonneg (Nat.cast_nonneg M) hu
    nlinarith
  rw [swap_circle_Ioi _ (cS : ℂ) ρS hρS.le _ C0 hε hcont hbd]
  have hin : ∀ w ∈ sphere (cS : ℂ) ρS, (∫ u in Set.Ioi (0 : ℝ), exp (((M : ℂ) * (w - z)) * u) * K w) =
      (M : ℂ)⁻¹ * ((Pa π a).eval w / w ^ M / (z - w)) := by
    intro w hw
    have hw0 := h0 w hw
    have hwre := re_le_of_mem_closedBall cS ρS w (sphere_subset_closedBall hw)
    have hwz : w - z ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hzw : z - w ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hre : ((M : ℂ) * (w - z)).re < 0 := by
      have : ((M : ℂ) * (w - z)).re = M * (w.re - z.re) := by simp
      rw [this]
      exact mul_neg_of_pos_of_neg (Nat.cast_pos.2 hM) (by linarith)
    rw [MeasureTheory.integral_mul_const, integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [Pa_eval]
    simp only [hK]
    field_simp
    ring
  rw [circleIntegral.integral_congr hρS.le hin, circleIntegral.integral_const_mul,
    circ_poly_div (Pa π a) M (Pa_natDegree M hNM π a) _ _ hS0 z hzout]
  have h2 := two_pi_I_ne_zero
  field_simp

/-- `∫_0^∞ β_a α_b = (2πi)⁻¹ M⁻¹ ∮_Γ Π_{j>b}(π_j - z) p_a(z) / P(z) dz`. -/
theorem beta_alpha_integral {N : ℕ} (M : ℕ) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ)
    (q cΓ ρΓ cS ρS : ℝ) (hρΓ : 0 ≤ ρΓ) (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS)
    (hsep : cS + ρS < cΓ - ρΓ) (hP : ∀ z ∈ sphere (cΓ : ℂ) ρΓ, Pz π z ≠ 0) (a b : Fin N) :
    ∫ u in Set.Ioi (0 : ℝ), (beta M π q cS ρS a u : ℂ) * (alpha M π q cΓ ρΓ b u : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ((M : ℂ)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ),
        (∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) * (Pa π a).eval z / Pz π z) := by
  have hρS : 0 < ρS := lt_of_le_of_lt dist_nonneg hS0
  have h0 : ∀ w ∈ sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at hS0; linarith
  have hcs : 0 < cS + ρS := by
    rw [mem_ball, dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hS0
    linarith [neg_abs_le cS]
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set g : ℂ → ℂ := fun z => z ^ M * (∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) /
    Pz π z with hg
  have hgc : ContinuousOn g (sphere (cΓ : ℂ) ρΓ) :=
    ContinuousOn.div (by fun_prop) (by unfold Pz; fun_prop) hP
  obtain ⟨C0, hC0⟩ := (isCompact_sphere (cΓ : ℂ) ρΓ).exists_bound_of_continuousOn hgc
  obtain ⟨Cb, hCb⟩ := beta_bound M π q cS ρS hρS.le h0 a
  have ha : ∀ u : ℝ, (alpha M π q cΓ ρΓ b u : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ), Ak M π q u b z := by
    intro u; rw [circ_eq_alpha, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have eA : ∀ (u : ℝ) (z : ℂ), (beta M π q cS ρS a u : ℂ) * Ak M π q u b z =
      ((beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q))) * g z := by
    intro u z; simp only [hg, Ak]; ring
  have step1 : ∀ u : ℝ, (beta M π q cS ρS a u : ℂ) * (alpha M π q cΓ ρΓ b u : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((cΓ : ℂ), ρΓ),
        ((beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q))) * g z := by
    intro u
    rw [ha]
    simp only [← eA]
    rw [circleIntegral.integral_const_mul]
    ring
  simp_rw [step1]
  rw [MeasureTheory.integral_const_mul]
  have hδ : 0 < (M : ℝ) * ((cΓ - ρΓ) - (cS + ρS)) := mul_pos (Nat.cast_pos.2 hM) (by linarith)
  have hcont : ContinuousOn (Function.uncurry fun (u : ℝ) (z : ℂ) =>
      ((beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q))) * g z)
      (Set.univ ×ˢ sphere (cΓ : ℂ) ρΓ) := by
    show ContinuousOn (fun p : ℝ × ℂ =>
      ((beta M π q cS ρS a p.1 : ℂ) * exp (-(p.1 : ℂ) * M * (p.2 - q))) * g p.2) _
    have hbc := beta_continuous M π q cS ρS hρS.le h0 a
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (hgc.comp continuousOn_snd (fun p hp => hp.2))
    exact (Complex.continuous_ofReal.comp (hbc.comp continuous_fst)).mul (by fun_prop)
  have hbd : ∀ u : ℝ, 0 ≤ u → ∀ z ∈ sphere (cΓ : ℂ) ρΓ,
      ‖((beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q))) * g z‖ ≤
        (|Cb| * C0) * Real.exp (-((M : ℝ) * ((cΓ - ρΓ) - (cS + ρS))) * u) := by
    intro u hu z hz
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp]
    have h1 : |beta M π q cS ρS a u| ≤ |Cb| * Real.exp (u * M * (cS + ρS - q)) :=
      (hCb u hu).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    have h2 : Real.exp (-(u : ℂ) * M * (z - q)).re ≤ Real.exp (-(u * M * (cΓ - ρΓ - q))) := by
      apply Real.exp_le_exp.2
      have hre : (-(u : ℂ) * M * (z - q)).re = -(u * M * (z.re - q)) := by simp
      rw [hre]
      have := le_re_of_mem_sphere cΓ ρΓ z hz
      have huM : 0 ≤ u * M := mul_nonneg hu (Nat.cast_nonneg M)
      nlinarith
    have h3 := hC0 z hz
    have he : Real.exp (u * M * (cS + ρS - q)) * Real.exp (-(u * M * (cΓ - ρΓ - q))) =
        Real.exp (-((M : ℝ) * ((cΓ - ρΓ) - (cS + ρS))) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |beta M π q cS ρS a u| * Real.exp (-(u : ℂ) * M * (z - q)).re * ‖g z‖
        ≤ (|Cb| * Real.exp (u * M * (cS + ρS - q))) * Real.exp (-(u * M * (cΓ - ρΓ - q))) * C0 := by
          gcongr
      _ = (|Cb| * C0) * Real.exp (-((M : ℝ) * ((cΓ - ρΓ) - (cS + ρS))) * u) := by
          rw [← he]; ring
  rw [swap_circle_Ioi _ (cΓ : ℂ) ρΓ hρΓ _ _ hδ hcont hbd]
  have hin : ∀ z ∈ sphere (cΓ : ℂ) ρΓ, (∫ u in Set.Ioi (0 : ℝ),
      ((beta M π q cS ρS a u : ℂ) * exp (-(u : ℂ) * M * (z - q))) * g z) =
      (M : ℂ)⁻¹ * ((∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) *
        (Pa π a).eval z / Pz π z) := by
    intro z hz
    have hzre : cS + ρS < z.re := by have := le_re_of_mem_sphere cΓ ρΓ z hz; linarith
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hzre; linarith
    have hPz := hP z hz
    rw [MeasureTheory.integral_mul_const, beta_laplace M hM hNM π q cS ρS hS0 a z hzre]
    simp only [hg]
    field_simp
  rw [circleIntegral.integral_congr hρΓ hin, circleIntegral.integral_const_mul]

/-- The `z`-contour evaluation: `∮_Γ Π_{j>b}(π_j - z) p_a(z) / P(z) dz = -2πi δ_ab`. -/
theorem z_eval {N : ℕ} (π : Fin N → ℝ) (cΓ ρΓ : ℝ)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (cΓ : ℂ) ρΓ) (a b : Fin N) :
    (∮ z in C((cΓ : ℂ), ρΓ), (∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) *
        (Pa π a).eval z / Pz π z) =
      if a = b then -(2 * (Real.pi : ℂ) * I) else 0 := by
  have hρΓ : 0 < ρΓ := lt_of_le_of_lt dist_nonneg (hπ a)
  have hPz := Pz_ne_of_ball π cΓ ρΓ hπ
  simp_rw [Pa_eval]
  rcases lt_or_ge b a with hba | hab
  · rw [if_neg (by intro h; rw [h] at hba; exact lt_irrefl _ hba)]
    have hu : Finset.univ.filter (fun j : Fin N => b < j) ∪ Finset.univ.filter (fun j => j < a) =
        Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_contra h
      push_neg at h
      exact absurd (lt_of_le_of_lt (h.1) (lt_of_lt_of_le hba h.2)) (lt_irrefl _)
    have key : ∀ z ∈ sphere (cΓ : ℂ) ρΓ,
        (∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) *
          (∏ j ∈ Finset.univ.filter (fun j => j < a), ((π j : ℂ) - z)) / Pz π z =
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => b < j) ∩ Finset.univ.filter (fun j => j < a),
          ((π j : ℂ) - z) := by
      intro z hz
      have hne := hPz z hz
      rw [← Finset.prod_union_inter, hu]
      unfold Pz at hne ⊢
      field_simp
    rw [circleIntegral.integral_congr hρΓ.le key]
    exact cauchy_entire _ (by fun_prop) _ _ hρΓ.le
  · set S := Finset.univ.filter (fun j : Fin N => a ≤ j ∧ j ≤ b) with hSdef
    have hd : Disjoint (Finset.univ.filter (fun j : Fin N => b < j))
        (Finset.univ.filter (fun j => j < a)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact absurd (lt_of_le_of_lt hab (lt_trans h1 h2)) (lt_irrefl _)
    have hc : Finset.univ.filter (fun j : Fin N => b < j) ∪ Finset.univ.filter (fun j => j < a) =
        Finset.univ.filter (fun j => ¬ (a ≤ j ∧ j ≤ b)) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or,
        not_le]
      constructor <;> intro h <;> rcases h with h | h <;> simp [h]
    have hsplit : ∀ z, Pz π z = (∏ j ∈ S, ((π j : ℂ) - z)) *
        ((∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) *
          (∏ j ∈ Finset.univ.filter (fun j => j < a), ((π j : ℂ) - z))) := by
      intro z
      rw [← Finset.prod_union hd, hc]
      unfold Pz
      exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have key : ∀ z ∈ sphere (cΓ : ℂ) ρΓ,
        (∏ j ∈ Finset.univ.filter (fun j => b < j), ((π j : ℂ) - z)) *
          (∏ j ∈ Finset.univ.filter (fun j => j < a), ((π j : ℂ) - z)) / Pz π z =
        (∏ j ∈ S, ((π j : ℂ) - z))⁻¹ := by
      intro z hz
      have hne := hPz z hz
      rw [hsplit z] at hne ⊢
      have h2 := right_ne_zero_of_mul hne
      rw [mul_comm (∏ j ∈ S, ((π j : ℂ) - z)), ← div_div, div_self h2, one_div]
    rw [circleIntegral.integral_congr hρΓ.le key]
    rcases eq_or_lt_of_le hab with h | h
    · subst h
      rw [if_pos rfl]
      have hS : S = {a} := by
        ext j
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hj; exact le_antisymm hj.2 hj.1
        · intro hj; rw [hj]; exact ⟨le_rfl, le_rfl⟩
      rw [hS]
      simp only [Finset.prod_singleton]
      have e : (fun z : ℂ => ((π a : ℂ) - z)⁻¹) = fun z => -(z - (π a : ℂ))⁻¹ := by
        funext z; rw [← neg_sub, inv_neg]
      have e2 : (fun z : ℂ => -(z - (π a : ℂ))⁻¹) = fun z => (-1 : ℂ) * (z - (π a : ℂ))⁻¹ := by
        funext z; ring
      rw [e, e2, circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hπ a)]
      ring
    · rw [if_neg (ne_of_lt h)]
      refine circle_inv_prod_eq_zero S ?_ (fun j => (π j : ℂ)) _ _ (fun j _ => hπ j)
      have hsub : ({a, b} : Finset (Fin N)) ⊆ S := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl
        · exact ⟨le_rfl, h.le⟩
        · exact ⟨h.le, le_rfl⟩
      have hcard := Finset.card_le_card hsub
      rwa [Finset.card_pair (ne_of_lt h)] at hcard

/-- D1 BIORTHOGONALITY (all `π`, coinciding allowed): `∫_0^∞ β_a (-M α_b) = δ_ab`. -/
theorem biorth {N : ℕ} (M : ℕ) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (cΓ : ℂ) ρΓ) (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS)
    (hsep : cS + ρS < cΓ - ρΓ) (a b : Fin N) :
    ∫ u in Set.Ioi (0 : ℝ), beta M π q cS ρS a u * (-(M : ℝ) * alpha M π q cΓ ρΓ b u) =
      if a = b then 1 else 0 := by
  have hρΓ : 0 < ρΓ := lt_of_le_of_lt dist_nonneg (hπ a)
  have hPz := Pz_ne_of_ball π cΓ ρΓ hπ
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ u : ℝ, ((beta M π q cS ρS a u * (-(M : ℝ) * alpha M π q cΓ ρΓ b u) : ℝ) : ℂ) =
      -(M : ℂ) * ((beta M π q cS ρS a u : ℂ) * (alpha M π q cΓ ρΓ b u : ℂ)) := by
    intro u; push_cast; ring
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul,
    beta_alpha_integral M hM hNM π q cΓ ρΓ cS ρS hρΓ.le hS0 hsep hPz a b, z_eval π cΓ ρΓ hπ a b]
  split_ifs
  · rw [show -(M : ℂ) * ((2 * (Real.pi : ℂ) * I)⁻¹ * ((M : ℂ)⁻¹ * -(2 * (Real.pi : ℂ) * I))) =
        ((M : ℂ) * (M : ℂ)⁻¹) * ((2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (Real.pi : ℂ) * I)) by ring,
      mul_inv_cancel₀ hM', inv_mul_cancel₀ two_pi_I_ne_zero, mul_one, Complex.ofReal_one]
  · simp

end B4196D

end


open SpikedWishart.SoftEdge in
/-- B + C: under the hypotheses of Proposition 2.1 the Fredholm determinant is a finite `N × N`
determinant `det(1 - A)`, `A_ab = ∫_ξ^∞ β_a(u) (-M α_b(u)) du`. -/
theorem B4196.fredholm_kernelKMN_eq_det (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (ℓ : Fin N → ℝ) (q : ℝ) (cΓ ρΓ : ℝ) (hΓ_encl : ∀ j, |(ℓ j)⁻¹ - cΓ| < ρΓ)
    (hΓ_right : q < cΓ - ρΓ) (cS ρS : ℝ) (hS_encl : |cS| < ρS) (hS_left : cS + ρS < q)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    fredholmDet (kernelKMN M (fun j => (ℓ j)⁻¹) q cΓ ρΓ cS ρS) ξ =
      (1 - Matrix.of fun a b : Fin N => ∫ u in Set.Ioi ξ,
        B4196B.beta M (fun j => (ℓ j)⁻¹) q cS ρS a u *
          (-(M : ℝ) * B4196B.alpha M (fun j => (ℓ j)⁻¹) q cΓ ρΓ b u)).det := by
  have hρΓ : 0 ≤ ρΓ := le_trans (abs_nonneg _) (hΓ_encl ⟨0, hN⟩).le
  have hρS : 0 ≤ ρS := le_trans (abs_nonneg _) hS_encl.le
  have hsep : cS + ρS < cΓ - ρΓ := by linarith
  have hM : 0 < M := by omega
  have hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, B4196B.Pz (fun j => (ℓ j)⁻¹) z ≠ 0 := by
    intro z hz
    rw [B4196B.Pz, Finset.prod_ne_zero_iff]
    intro j _ h
    rw [mem_sphere_iff_norm] at hz
    have h' : z = (((ℓ j)⁻¹ : ℝ) : ℂ) := (sub_eq_zero.1 h).symm
    rw [h', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hz
    linarith [hΓ_encl j]
  have h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h
    rw [mem_sphere_iff_norm, h, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hw
    linarith
  exact B4196.fredholmDet_finiteRank N
    (fun a u => -(M : ℝ) * B4196B.alpha M (fun j => (ℓ j)⁻¹) q cΓ ρΓ a u)
    (fun a v => B4196B.beta M (fun j => (ℓ j)⁻¹) q cS ρS a v) _ ξ
    (fun u v _ _ => B4196B.kernelKMN_finiteRank M _ q cΓ ρΓ cS ρS hρΓ hρS hsep hP h0 u v)
    (fun a b => B4196B.integrableOn_phi_psi M hM _ q cΓ ρΓ cS ρS hρΓ hρS hsep hP h0 ξ hξ a b)

section
open MeasureTheory Complex Metric

/-- `1 - A(ξ) = (∫_0^ξ β_a (-M α_b))_{ab}` (from D1 biorthogonality). -/
theorem B4196D.one_sub_A_eq {N : ℕ} (M : ℕ) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ)
    (q cΓ ρΓ cS ρS : ℝ) (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (cΓ : ℂ) ρΓ)
    (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS) (hsep : cS + ρS < cΓ - ρΓ) (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (1 - Matrix.of fun a b : Fin N => ∫ u in Set.Ioi ξ,
        B4196B.beta M π q cS ρS a u * (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)) =
      Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ,
        B4196B.beta M π q cS ρS a u * (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u) := by
  have hρS : 0 < ρS := lt_of_le_of_lt dist_nonneg hS0
  have h0 : ∀ w ∈ sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at hS0; linarith
  ext a b
  have hρΓ : 0 < ρΓ := lt_of_le_of_lt dist_nonneg (hπ a)
  have hP := B4196D.Pz_ne_of_ball π cΓ ρΓ hπ
  have hint : IntegrableOn (fun u => B4196B.beta M π q cS ρS a u *
      (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)) (Set.Ioi 0) :=
    (B4196B.integrableOn_phi_psi M hM π q cΓ ρΓ cS ρS hρΓ.le hρS.le hsep hP h0 0 le_rfl b a).congr_fun
      (fun u _ => mul_comm _ _) measurableSet_Ioi
  have hsplit := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := ξ))
    measurableSet_Ioi (hint.mono_set Set.Ioc_subset_Ioi_self)
    (hint.mono_set (Set.Ioi_subset_Ioi hξ))
  rw [Set.Ioc_union_Ioi_eq_Ioi hξ, B4196D.biorth M hM hNM π q cΓ ρΓ cS ρS hπ hS0 hsep a b] at hsplit
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
  rw [hsplit]
  ring

end

open SpikedWishart.SoftEdge in
/-- DET SIDE of Proposition 2.1 (all `π`, coinciding allowed):
`fredholmDet K_{M,N} ξ = det (∫_0^ξ β_a (-M α_b))_{a,b<N}`. -/
theorem B4196.det_side (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (ℓ : Fin N → ℝ) (q : ℝ) (cΓ ρΓ : ℝ) (hΓ_encl : ∀ j, |(ℓ j)⁻¹ - cΓ| < ρΓ)
    (hΓ_right : q < cΓ - ρΓ) (cS ρS : ℝ) (hS_encl : |cS| < ρS) (hS_left : cS + ρS < q)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    fredholmDet (kernelKMN M (fun j => (ℓ j)⁻¹) q cΓ ρΓ cS ρS) ξ =
      (Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ,
        B4196B.beta M (fun j => (ℓ j)⁻¹) q cS ρS a u *
          (-(M : ℝ) * B4196B.alpha M (fun j => (ℓ j)⁻¹) q cΓ ρΓ b u)).det := by
  have hπ : ∀ j, ((((ℓ j)⁻¹ : ℝ) : ℝ) : ℂ) ∈ Metric.ball (cΓ : ℂ) ρΓ := by
    intro j
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hΓ_encl j
  have hS0 : (0 : ℂ) ∈ Metric.ball (cS : ℂ) ρS := by
    rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact hS_encl
  rw [B4196.fredholm_kernelKMN_eq_det M N hN hNM ℓ q cΓ ρΓ hΓ_encl hΓ_right cS ρS hS_encl hS_left ξ hξ,
    B4196D.one_sub_A_eq M (by omega) hNM _ q cΓ ρΓ cS ρS hπ hS0 (by linarith) ξ hξ]

section
open MeasureTheory Complex Metric

namespace B4196D

/-- Fubini on a finite interval: swap `∫_{(0,y]}` with a circle integral (continuous integrand). -/
theorem swap_circle_Ioc (F : ℝ → ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (y : ℝ)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ sphere c R)) :
    ∫ t in Set.Ioc (0 : ℝ) y, (∮ z in C(c, R), F t z) =
      ∮ z in C(c, R), ∫ t in Set.Ioc (0 : ℝ) y, F t z := by
  simp only [circleIntegral_def_Icc]
  have hsm : ∀ θ : ℝ, (∫ t in Set.Ioc (0 : ℝ) y, deriv (circleMap c R) θ • F t (circleMap c R θ)) =
      deriv (circleMap c R) θ • ∫ t in Set.Ioc (0 : ℝ) y, F t (circleMap c R θ) :=
    fun θ => integral_smul _ _
  simp_rw [← hsm]
  refine integral_integral_swap ?_
  have hcont : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2 • F p.1 (circleMap c R p.2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => F p.1 (circleMap c R p.2)) :=
      hF.comp_continuous (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
        (fun p => ⟨Set.mem_univ _, circleMap_mem_sphere c hR p.2⟩)
    have h2 : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2) := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    exact h2.smul h1
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)

/-- `(2πi)⁻¹ ∮ e^{wy} / w^{m+1} dw = y^m / m!` for `0` inside the circle. -/
theorem E_explicit (c : ℂ) (r : ℝ) (h0 : (0 : ℂ) ∈ ball c r) (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C(c, r), exp (w * y) / w ^ (m + 1) =
      (y : ℂ) ^ m / (m.factorial : ℂ) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h0
  have hw0 : ∀ w ∈ sphere c r, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at h0; linarith
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := two_pi_I_ne_zero
  induction m generalizing y with
  | zero =>
    have e : ∀ w ∈ sphere c r, exp (w * y) / w ^ (0 + 1) = (w - 0)⁻¹ • exp (w * y) := by
      intro w _; rw [sub_zero, smul_eq_mul, zero_add, pow_one, div_eq_inv_mul]
    rw [circleIntegral.integral_congr hr.le e,
      circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty h0
        (by fun_prop) (fun x _ => by fun_prop)]
    simp only [zero_mul, exp_zero, smul_eq_mul, mul_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one]
    exact inv_mul_cancel₀ h2
  | succ m ih =>
    have hzero : (∮ w in C(c, r), 1 / w ^ (m + 2)) = 0 := by
      have e : ∀ w ∈ sphere c r, 1 / w ^ (m + 2) = (w - 0) ^ (-((m : ℤ) + 2)) := by
        intro w _
        rw [sub_zero, zpow_neg, one_div, show ((m : ℤ) + 2) = ((m + 2 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
      rw [circleIntegral.integral_congr hr.le e, circleIntegral.integral_sub_zpow_of_ne (by omega)]
    have hint : ∀ w ∈ sphere c r, exp (w * y) / w ^ (m + 1 + 1) =
        (∫ t in Set.Ioc (0 : ℝ) y, exp (w * t) / w ^ (m + 1)) + 1 / w ^ (m + 2) := by
      intro w hw
      have hw' := hw0 w hw
      rw [integral_div, ← intervalIntegral.integral_of_le hy,
        integral_exp_mul_complex hw']
      simp only [Complex.ofReal_zero, mul_zero, exp_zero]
      field_simp
      ring
    have hI1 : CircleIntegrable (fun w => ∫ t in Set.Ioc (0 : ℝ) y, exp (w * t) / w ^ (m + 1)) c r := by
      refine ContinuousOn.circleIntegrable hr.le ?_
      have e : ∀ w ∈ sphere c r, (∫ t in Set.Ioc (0 : ℝ) y, exp (w * t) / w ^ (m + 1)) =
          exp (w * y) / w ^ (m + 1 + 1) - 1 / w ^ (m + 2) := by
        intro w hw; rw [hint w hw]; ring
      refine ContinuousOn.congr ?_ e
      refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun w hw => pow_ne_zero _ (hw0 w hw))) (ContinuousOn.div continuousOn_const (by fun_prop)
        (fun w hw => pow_ne_zero _ (hw0 w hw)))
    have hI2 : CircleIntegrable (fun w : ℂ => 1 / w ^ (m + 2)) c r :=
      ContinuousOn.circleIntegrable hr.le (ContinuousOn.div continuousOn_const (by fun_prop)
        (fun w hw => pow_ne_zero _ (hw0 w hw)))
    rw [circleIntegral.integral_congr hr.le hint, circleIntegral.integral_add hI1 hI2, hzero, add_zero]
    have hcont : ContinuousOn (Function.uncurry fun (t : ℝ) (w : ℂ) => exp (w * t) / w ^ (m + 1))
        (Set.univ ×ˢ sphere c r) := by
      show ContinuousOn (fun p : ℝ × ℂ => exp (p.2 * (p.1 : ℂ)) / p.2 ^ (m + 1)) _
      exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun p hp => pow_ne_zero _ (hw0 p.2 hp.2))
    rw [← swap_circle_Ioc _ c r hr.le y hcont, ← MeasureTheory.integral_const_mul]
    have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) y, (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∮ w in C(c, r), exp (w * t) / w ^ (m + 1)) = (((t ^ m / (m.factorial : ℝ)) : ℝ) : ℂ) := by
      intro t ht
      rw [ih t (le_of_lt ht.1)]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_complex_ofReal,
      ← intervalIntegral.integral_of_le hy, intervalIntegral.integral_div, integral_pow]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    field_simp
    ring

end B4196D


namespace B4196D
open B4196B

/-- G3: explicit form of `β_a` (residue at `0`): `β_a(u) = e^{-uMq} Σ_{i<M} [p_a]_i (uM)^{M-1-i}/(M-1-i)!`. -/
theorem beta_explicit {N : ℕ} (M : ℕ) (hNM : N ≤ M) (π : Fin N → ℝ) (q cS ρS : ℝ)
    (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS) (a : Fin N) (u : ℝ) (hu : 0 ≤ u) :
    (beta M π q cS ρS a u : ℂ) = exp (-(u : ℂ) * M * q) *
      ∑ i ∈ Finset.range M, (Pa π a).coeff i * ((u * M : ℝ) : ℂ) ^ (M - 1 - i) /
        ((M - 1 - i).factorial : ℂ) := by
  have hρS : 0 < ρS := lt_of_le_of_lt dist_nonneg hS0
  have h0 : ∀ w ∈ sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h; rw [h, mem_sphere] at hw; rw [mem_ball] at hS0; linarith
  have hb : (beta M π q cS ρS a u : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ w in C((cS : ℂ), ρS), Bk M π q u a w := by
    rw [circ_eq_beta, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have e : ∀ w ∈ sphere (cS : ℂ) ρS, Bk M π q u a w = ∑ i ∈ Finset.range M,
      (exp (-(u : ℂ) * M * q) * (Pa π a).coeff i) *
        (exp (w * ((u * M : ℝ) : ℂ)) / w ^ (M - 1 - i + 1)) := by
    intro w hw
    have hw' := h0 w hw
    unfold Bk
    rw [← Pa_eval, Polynomial.eval_eq_sum_range' (Pa_natDegree M hNM π a), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < M := Finset.mem_range.1 hi
    rw [show M - 1 - i + 1 = M - i by omega]
    have hp : w ^ M = w ^ (M - i) * w ^ i := by rw [← pow_add]; congr 1; omega
    rw [hp, show ((u : ℂ) * M * (w - q)) = w * ((u * M : ℝ) : ℂ) + (-(u : ℂ) * M * q) by push_cast; ring,
      exp_add]
    have h1 : w ^ (M - i) ≠ 0 := pow_ne_zero _ hw'
    have h2 : w ^ i ≠ 0 := pow_ne_zero _ hw'
    field_simp
  have hint : ∀ i ∈ Finset.range M, CircleIntegrable (fun w => (exp (-(u : ℂ) * M * q) *
      (Pa π a).coeff i) * (exp (w * ((u * M : ℝ) : ℂ)) / w ^ (M - 1 - i + 1))) (cS : ℂ) ρS := by
    intro i _
    refine ContinuousOn.circleIntegrable hρS.le ?_
    exact continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun w hw => pow_ne_zero _ (h0 w hw)))
  rw [hb, circleIntegral.integral_congr hρS.le e, circ_finset_sum _ _ _ _ hint, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [circleIntegral.integral_const_mul, mul_left_comm,
    E_explicit (cS : ℂ) ρS hS0 (M - 1 - i) (u * M) (mul_nonneg hu (Nat.cast_nonneg M))]
  ring

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

/-- Fubini on a finite interval `(a,b]`: swap with a circle integral (continuous integrand). -/
theorem swap_circle_Ioc' (F : ℝ → ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (a b : ℝ)
    (hF : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ sphere c R)) :
    ∫ t in Set.Ioc a b, (∮ z in C(c, R), F t z) =
      ∮ z in C(c, R), ∫ t in Set.Ioc a b, F t z := by
  simp only [circleIntegral_def_Icc]
  have hsm : ∀ θ : ℝ, (∫ t in Set.Ioc a b, deriv (circleMap c R) θ • F t (circleMap c R θ)) =
      deriv (circleMap c R) θ • ∫ t in Set.Ioc a b, F t (circleMap c R θ) :=
    fun θ => integral_smul _ _
  simp_rw [← hsm]
  refine integral_integral_swap ?_
  have hcont : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2 • F p.1 (circleMap c R p.2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => F p.1 (circleMap c R p.2)) :=
      hF.comp_continuous (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
        (fun p => ⟨Set.mem_univ _, circleMap_mem_sphere c hR p.2⟩)
    have h2 : Continuous (fun p : ℝ × ℝ => deriv (circleMap c R) p.2) := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    exact h2.smul h1
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self le_rfl)

/-- `∫_{(a,b]} e^{-t c} dt = (e^{-a c} - e^{-b c}) / c`. -/
theorem integral_exp_neg_Ioc (c : ℂ) (hc : c ≠ 0) (a b : ℝ) (hab : a ≤ b) :
    ∫ t in Set.Ioc a b, exp (-(t : ℂ) * c) = (exp (-(a : ℂ) * c) - exp (-(b : ℂ) * c)) / c := by
  have e : ∀ t : ℝ, exp (-(t : ℂ) * c) = exp ((-c) * t) := fun t => by ring_nf
  simp_rw [e]
  rw [← intervalIntegral.integral_of_le hab, integral_exp_mul_complex (neg_ne_zero.2 hc)]
  rw [show (-c) * (b : ℂ) = -(b : ℂ) * c by ring, show (-c) * (a : ℂ) = -(a : ℂ) * c by ring]
  field_simp
  ring

section rows
open ComplexConjugate

/-- conj symmetry -> circle integral purely imaginary (copy of draft lemma). -/
theorem conj_circleIntegral' (f : ℂ → ℂ) (c R : ℝ) (hf : ∀ z, f (conj z) = conj (f z)) :
    conj (∮ z in C((c : ℂ), R), f z) = -(∮ z in C((c : ℂ), R), f z) := by
  unfold circleIntegral
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have key : ∀ θ : ℝ, conj (deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ)) =
      -(deriv (circleMap (c : ℂ) R) (-θ) • f (circleMap (c : ℂ) R (-θ))) := by
    intro θ
    simp only [deriv_circleMap, smul_eq_mul, map_mul, conj_I, ← hf,
      conj_circleMap, conj_ofReal, map_zero]
    ring
  rw [intervalIntegral.integral_of_le h2π, ← integral_conj, ← intervalIntegral.integral_of_le h2π]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg
    (fun θ => deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ))]
  congr 1
  have hper : Function.Periodic
      (fun θ => deriv (circleMap (c : ℂ) R) θ • f (circleMap (c : ℂ) R θ)) (2 * Real.pi) := by
    intro θ
    simp only [deriv_circleMap, periodic_circleMap _ _ θ]
  have := hper.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  simp only [neg_add_cancel, zero_add] at this
  rw [← intervalIntegral.integral_of_le h2π]
  simpa using this

theorem real_of_conj' (X : ℂ) (hX : conj X = -X) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * X = ((((2 * (Real.pi : ℂ) * I)⁻¹ * X).re : ℝ) : ℂ) := by
  refine (Complex.conj_eq_iff_re.1 ?_).symm
  rw [map_mul, map_inv₀, hX]
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I, mul_neg, inv_neg, neg_mul, neg_neg]

/-- contour row `(2πi)⁻¹ ∮ e^{-xz} g(z) dz` (complex) and its real part. -/
noncomputable def rowC (g : ℂ → ℂ) (c R : ℝ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((c : ℂ), R), exp (-(x : ℂ) * z) * g z

noncomputable def row (g : ℂ → ℂ) (c R : ℝ) (x : ℝ) : ℝ := (rowC g c R x).re

theorem rowC_eq (g : ℂ → ℂ) (c R : ℝ) (hg : ∀ z, g (conj z) = conj (g z)) (x : ℝ) :
    rowC g c R x = (row g c R x : ℂ) := by
  unfold row rowC
  refine real_of_conj' _ (conj_circleIntegral' _ c R (fun z => ?_))
  simp only [map_mul, ← exp_conj, map_neg, conj_ofReal, hg]

theorem row_continuous (g : ℂ → ℂ) (c R : ℝ) (hR : 0 ≤ R) (hg : ContinuousOn g (sphere (c : ℂ) R)) :
    Continuous (row g c R) := by
  have hgc : Continuous (fun φ : ℝ => g (circleMap (c : ℂ) R φ)) :=
    hg.comp_continuous (continuous_circleMap _ R) (fun φ => circleMap_mem_sphere _ hR φ)
  have hc : Continuous (fun x : ℝ => ∮ z in C((c : ℂ), R), exp (-(x : ℂ) * z) * g z) := by
    unfold circleIntegral
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * Real.pi)
    have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap (c : ℂ) R) p.2 := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    have h3 : Continuous fun p : ℝ × ℝ => exp (-(p.1 : ℂ) * circleMap (c : ℂ) R p.2) := by fun_prop
    exact h1.smul (h3.mul (hgc.comp continuous_snd))
  exact Complex.continuous_re.comp (continuous_const.mul hc)

/-- 1D antiderivative of a weighted row: `∫_{(a,b]} e^{pt} row_g(t) dt = e^{pa} row_{g'}(a) - e^{pb} row_{g'}(b)`,
`g'(z) = g(z)/(z-p)`. -/
theorem integral_exp_row (g : ℂ → ℂ) (c R : ℝ) (hR : 0 ≤ R) (hg : ContinuousOn g (sphere (c : ℂ) R))
    (hgc : ∀ z, g (conj z) = conj (g z)) (p : ℝ) (hp : ∀ z ∈ sphere (c : ℂ) R, z - p ≠ 0)
    (a b : ℝ) (hab : a ≤ b) :
    ∫ t in Set.Ioc a b, Real.exp (p * t) * row g c R t =
      Real.exp (p * a) * row (fun z => g z / (z - p)) c R a -
        Real.exp (p * b) * row (fun z => g z / (z - p)) c R b := by
  have hgc' : ∀ z, (fun z => g z / (z - p)) (conj z) = conj ((fun z => g z / (z - p)) z) := by
    intro z; simp only [map_div₀, map_sub, conj_ofReal, hgc]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [← rowC_eq _ c R hgc' a, ← rowC_eq _ c R hgc' b]
  have e1 : ∀ t : ℝ, exp ((p : ℂ) * t) * (row g c R t : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C((c : ℂ), R), exp ((p : ℂ) * t) * exp (-(t : ℂ) * z) * g z := by
    intro t
    rw [← rowC_eq g c R hgc t, rowC, mul_left_comm, ← circleIntegral.integral_const_mul]
    congr 1
    refine circleIntegral.integral_congr hR (fun z _ => ?_)
    ring
  simp_rw [e1]
  rw [integral_const_mul]
  have hcont : ContinuousOn (Function.uncurry fun (t : ℝ) (z : ℂ) =>
      exp ((p : ℂ) * t) * exp (-(t : ℂ) * z) * g z) (Set.univ ×ˢ sphere (c : ℂ) R) := by
    show ContinuousOn (fun q : ℝ × ℂ => exp ((p : ℂ) * q.1) * exp (-(q.1 : ℂ) * q.2) * g q.2) _
    refine ContinuousOn.mul (by fun_prop) (hg.comp continuousOn_snd (fun q hq => hq.2))
  rw [swap_circle_Ioc' _ _ R hR a b hcont, rowC, rowC]
  have hIa : CircleIntegrable (fun z => cexp ((p : ℂ) * a) * (cexp (-(a : ℂ) * z) * (g z / (z - p))))
      (c : ℂ) R := ContinuousOn.circleIntegrable hR
      (continuousOn_const.mul (ContinuousOn.mul (by fun_prop) (hg.div (by fun_prop) hp)))
  have hIb : CircleIntegrable (fun z => cexp ((p : ℂ) * b) * (cexp (-(b : ℂ) * z) * (g z / (z - p))))
      (c : ℂ) R := ContinuousOn.circleIntegrable hR
      (continuousOn_const.mul (ContinuousOn.mul (by fun_prop) (hg.div (by fun_prop) hp)))
  rw [show ∀ X Y : ℂ, cexp ((p : ℂ) * a) * ((2 * (Real.pi : ℂ) * I)⁻¹ * X) -
      cexp ((p : ℂ) * b) * ((2 * (Real.pi : ℂ) * I)⁻¹ * Y) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * (cexp ((p : ℂ) * a) * X - cexp ((p : ℂ) * b) * Y) from
      fun X Y => by ring]
  rw [← circleIntegral.integral_const_mul (cexp ((p : ℂ) * a)),
    ← circleIntegral.integral_const_mul (cexp ((p : ℂ) * b)), ← circleIntegral.integral_sub hIa hIb]
  congr 1
  refine circleIntegral.integral_congr hR (fun z hz => ?_)
  have hzp := hp z hz
  have e2 : ∀ t : ℝ, exp ((p : ℂ) * t) * exp (-(t : ℂ) * z) * g z =
      g z * exp (-(t : ℂ) * (z - p)) := fun t => by rw [mul_comm _ (g z), ← exp_add]; ring_nf
  simp_rw [e2]
  rw [integral_const_mul, integral_exp_neg_Ioc _ hzp a b hab]
  rw [show exp (-(a : ℂ) * (z - p)) = exp ((p : ℂ) * a) * exp (-(a : ℂ) * z) by
      rw [← exp_add]; ring_nf,
    show exp (-(b : ℂ) * (z - p)) = exp ((p : ℂ) * b) * exp (-(b : ℂ) * z) by
      rw [← exp_add]; ring_nf]
  push_cast
  field_simp

end rows

section moms
open ComplexConjugate

theorem row_congr (g g' : ℂ → ℂ) (c R : ℝ) (hR : 0 ≤ R) (h : ∀ z ∈ sphere (c : ℂ) R, g z = g' z) (x : ℝ) :
    row g c R x = row g' c R x := by
  unfold row rowC
  rw [circleIntegral.integral_congr (g := fun z => exp (-(x : ℂ) * z) * g' z) hR
    (fun z hz => by simp only [h z hz])]

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

/-- Cauchy: `row (z^M/(z-p)) x = e^{-px} p^M` for `p` inside the circle. -/
theorem row_cauchy (M : ℕ) (c R : ℝ) (p : ℝ) (hp : (p : ℂ) ∈ ball (c : ℂ) R) (x : ℝ) :
    row (fun z => z ^ M / (z - p)) c R x = Real.exp (-p * x) * p ^ M := by
  unfold row rowC
  have e : ∀ z ∈ sphere (c : ℂ) R, exp (-(x : ℂ) * z) * (z ^ M / (z - p)) =
      (z - p)⁻¹ • (exp (-(x : ℂ) * z) * z ^ M) := by
    intro z _; rw [smul_eq_mul]; field_simp
  have hR : 0 ≤ R := le_of_lt (lt_of_le_of_lt dist_nonneg hp)
  rw [circleIntegral.integral_congr hR e,
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty hp
      (by fun_prop) (fun z _ => by fun_prop)]
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have : exp (-(x : ℂ) * p) * (p : ℂ) ^ M = ((Real.exp (-p * x) * p ^ M : ℝ) : ℂ) := by
    push_cast; ring_nf
  rw [this, Complex.ofReal_re]

variable {N : ℕ}

/-- level-`n` denominator `Π_{j<n} (z - π_j)`. -/
noncomputable def den (π : Fin N → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < n), (z - π j)

/-- level-`n` moment functions `z^{M+i} / den_n(z)`. -/
noncomputable def gm (M : ℕ) (π : Fin N → ℝ) (n i : ℕ) (z : ℂ) : ℂ := z ^ (M + i) / den π n z

noncomputable def momMat (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (n : ℕ) (la : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => row (gm M π n i) c R (la k)

theorem den_succ (π : Fin N → ℝ) (n : ℕ) (hn : n < N) (z : ℂ) :
    den π (n + 1) z = den π n z * (z - π ⟨n, hn⟩) := by
  unfold den
  have hs : Finset.univ.filter (fun j : Fin N => (j : ℕ) < n + 1) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun j : Fin N => (j : ℕ) < n)) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hs, Finset.prod_insert (by simp), mul_comm]

theorem den_ne (π : Fin N → ℝ) (c R : ℝ) (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) (n : ℕ)
    (z : ℂ) (hz : z ∈ sphere (c : ℂ) R) : den π n z ≠ 0 := by
  unfold den
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have h' : z = (π j : ℂ) := sub_eq_zero.1 h
  rw [h'] at hz
  have := hπ j
  rw [mem_ball] at this; rw [mem_sphere] at hz; linarith

theorem gm_conj (M : ℕ) (π : Fin N → ℝ) (n i : ℕ) (z : ℂ) :
    gm M π n i (conj z) = conj (gm M π n i z) := by
  simp only [gm, den, map_div₀, map_pow, map_prod, map_sub, conj_ofReal]

theorem gm_cont (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R)
    (n i : ℕ) : ContinuousOn (gm M π n i) (sphere (c : ℂ) R) := by
  unfold gm
  exact ContinuousOn.div (by fun_prop) (by unfold den; fun_prop) (den_ne π c R hπ n)

/-- the real polynomial `Π_{j<n}(X - π_j)`. -/
noncomputable def Qn (π : Fin N → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < n), (Polynomial.X - Polynomial.C (π j))

theorem Qn_natDegree (π : Fin N → ℝ) (n : ℕ) : (Qn π n).natDegree < n + 1 := by
  have h1 : (Qn π n).natDegree ≤ (Finset.univ.filter (fun j : Fin N => (j : ℕ) < n)).card := by
    unfold Qn
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < n), 1 :=
          Finset.sum_le_sum (fun j _ => by rw [Polynomial.natDegree_X_sub_C])
      _ = _ := by simp
  have h2 : (Finset.univ.filter (fun j : Fin N => (j : ℕ) < n)).card ≤ n := by
    rw [Fin.card_filter_val_lt]; exact min_le_right _ _
  omega

theorem den_eq_sum (π : Fin N → ℝ) (n : ℕ) (z : ℂ) :
    den π n z = ∑ i ∈ Finset.range (n + 1), (((Qn π n).coeff i : ℝ) : ℂ) * z ^ i := by
  have h : den π n z = ((Qn π n).map (algebraMap ℝ ℂ)).eval z := by
    unfold den Qn
    rw [Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp
  rw [h, Polynomial.eval_eq_sum_range' (by rw [Polynomial.natDegree_map]; exact Qn_natDegree π n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_map]
  rfl

/-- row 0 of the level-`n+1` bordered matrix: `e^{-px} = p^{-M} Σ_i q_i row(gm_{n+1,i})(x)`. -/
theorem exp_row (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (hR : 0 ≤ R)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) (n : ℕ) (hn : n < N) (hp0 : π ⟨n, hn⟩ ≠ 0) (x : ℝ) :
    Real.exp (-(π ⟨n, hn⟩) * x) = ∑ i ∈ Finset.range (n + 1),
      ((π ⟨n, hn⟩) ^ M)⁻¹ * (Qn π n).coeff i * row (gm M π (n + 1) i) c R x := by
  set p := π ⟨n, hn⟩ with hpdef
  have hc := row_cauchy M c R p (hπ ⟨n, hn⟩) x
  have hcongr : ∀ z ∈ sphere (c : ℂ) R, z ^ M / (z - p) =
      ∑ i ∈ Finset.range (n + 1), (((Qn π n).coeff i : ℝ) : ℂ) * gm M π (n + 1) i z := by
    intro z hz
    have hd := den_ne π c R hπ (n + 1) z hz
    have hd' := den_ne π c R hπ n z hz
    unfold gm
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    have e : ∑ i ∈ Finset.range (n + 1), (((Qn π n).coeff i : ℝ) : ℂ) * z ^ (M + i) =
        z ^ M * den π n z := by
      rw [den_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_add]; ring
    rw [e, den_succ π n hn z, ← hpdef]
    have hzp : z - p ≠ 0 := by
      intro h; rw [den_succ π n hn z, ← hpdef, h, mul_zero] at hd; exact hd rfl
    field_simp
  rw [row_congr _ _ c R hR hcongr, row_sum _ _ _ c R hR
    (fun i _ => gm_cont M π c R hπ (n + 1) i)] at hc
  have hpM : (p ^ M : ℝ) ≠ 0 := pow_ne_zero _ hp0
  have : Real.exp (-p * x) = (p ^ M)⁻¹ * ∑ i ∈ Finset.range (n + 1),
      (Qn π n).coeff i * row (gm M π (n + 1) i) c R x := by
    rw [hc]; field_simp
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end moms

section stepsec
variable {N : ℕ}

/-- G2' STEP: integrating the level-`n` moment determinant over the interlacing box of `la`
(weight `e^{-π_n(|la|-|μ|)}`) gives a CONSTANT times the level-`n+1` moment determinant. -/
theorem gt_step (M : ℕ) (π : Fin N → ℝ) (c R : ℝ) (hR : 0 ≤ R)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) (n : ℕ) (hn : n < N) (hp0 : π ⟨n, hn⟩ ≠ 0) :
    ∃ C : ℝ, ∀ la : Fin (n + 1) → ℝ, StrictAnti la →
      ∫ μ in Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)),
        Real.exp (-(π ⟨n, hn⟩) * (∑ j, la j - ∑ i, μ i)) * (momMat M π c R n μ).det =
      C * (momMat M π c R (n + 1) la).det := by
  set p := π ⟨n, hn⟩ with hpdef
  set Cm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun (r i : Fin (n + 1)) =>
    (Fin.cases ((p ^ M)⁻¹ * (Qn π n).coeff (i : ℕ)) (fun r' : Fin n => if i = r'.castSucc then 1 else 0) r : ℝ)
    with hCm
  refine ⟨Cm.det, fun la hla => ?_⟩
  have hpz : ∀ z ∈ sphere (c : ℂ) R, z - (p : ℂ) ≠ 0 := by
    intro z hz h
    have h' : z = (p : ℂ) := sub_eq_zero.1 h
    have := hπ ⟨n, hn⟩
    rw [← hpdef, ← h'] at this
    rw [mem_ball] at this; rw [mem_sphere] at hz; linarith
  have hgm : ∀ (i : ℕ), ∀ z ∈ sphere (c : ℂ) R, gm M π n i z / (z - p) = gm M π (n + 1) i z := by
    intro i z hz
    unfold gm
    rw [den_succ π n hn z, ← hpdef, div_div]
  -- step 1: pull the weight into the columns
  have h1 : ∀ μ : Fin n → ℝ, Real.exp (-p * (∑ j, la j - ∑ i, μ i)) * (momMat M π c R n μ).det =
      Real.exp (-p * ∑ j, la j) *
        (Matrix.of fun (i k : Fin n) => Real.exp (p * μ k) * row (gm M π n i) c R (μ k)).det := by
    intro μ
    have e : (Matrix.of fun (i k : Fin n) => Real.exp (p * μ k) * row (gm M π n i) c R (μ k)) =
        Matrix.of fun (i k : Fin n) => (fun k => Real.exp (p * μ k)) k * momMat M π c R n μ i k := rfl
    rw [e, Matrix.det_mul_row, ← mul_assoc, ← Real.exp_sum, ← Real.exp_add, Finset.mul_sum]
    congr 2
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  -- step 2: box integral of the determinant
  have hcont : ∀ i : Fin n, Continuous (fun t => Real.exp (p * t) * row (gm M π n i) c R t) :=
    fun i => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (row_continuous _ c R hR (gm_cont M π c R hπ n i))
  rw [integral_box_det (fun (i : Fin n) t => Real.exp (p * t) * row (gm M π n i) c R t) _
    (fun i k => ((hcont i).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)]
  -- step 3: entries
  set h : Fin n → Fin (n + 1) → ℝ := fun i k => Real.exp (p * la k) * row (gm M π (n + 1) i) c R (la k)
    with hh
  have h3 : (Matrix.of fun (i k : Fin n) => ∫ t in Set.Ioc (la k.succ) (la k.castSucc),
      Real.exp (p * t) * row (gm M π n i) c R t) =
      -(Matrix.of fun (i k : Fin n) => h i k.castSucc - h i k.succ) := by
    ext i k
    have hlt : la k.succ ≤ la k.castSucc := (hla (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
    rw [Matrix.of_apply, integral_exp_row _ c R hR (gm_cont M π c R hπ n i) (gm_conj M π n i) p hpz _ _ hlt,
      row_congr _ _ c R hR (hgm i), row_congr _ _ c R hR (hgm i), Matrix.neg_apply, Matrix.of_apply]
    simp only [hh]
    ring
  rw [h3, Matrix.det_neg, Fintype.card_fin, det_border h]
  -- step 5: multiply columns by `e^{-p la_k}` and factor `Cm * momMat`
  have h5 : Real.exp (-p * ∑ j, la j) * (Matrix.of fun (i k : Fin (n + 1)) =>
      (Fin.cases (1 : ℝ) (fun i' => h i' k) i : ℝ)).det = (Cm * momMat M π c R (n + 1) la).det := by
    have e : (Cm * momMat M π c R (n + 1) la) = Matrix.of fun (i k : Fin (n + 1)) =>
        (fun k => Real.exp (-p * la k)) k * (Matrix.of fun (i k : Fin (n + 1)) =>
          (Fin.cases (1 : ℝ) (fun i' => h i' k) i : ℝ)) i k := by
      ext r k
      simp only [Matrix.mul_apply, Matrix.of_apply, hCm, momMat]
      cases r using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, mul_one]
        rw [exp_row M π c R hR hπ n hn hp0 (la k), ← hpdef,
          ← Fin.sum_univ_eq_sum_range (fun i => (p ^ M)⁻¹ * (Qn π n).coeff i * row (gm M π (n + 1) i) c R (la k))]
      | succ r' =>
        simp only [Fin.cases_succ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          hh, Fin.coe_castSucc]
        rw [← mul_assoc, ← Real.exp_add, show -p * la k + p * la k = 0 by ring, Real.exp_zero, one_mul]
    rw [e, Matrix.det_mul_row, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
  rw [Matrix.det_mul] at h5
  rw [← h5, ← mul_assoc ((-1 : ℝ) ^ n), ← mul_pow]
  norm_num

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

theorem Pa_card {N : ℕ} (a : Fin N) : (Finset.univ.filter (fun j : Fin N => j < a)).card = (a : ℕ) := by
  have h : Finset.univ.filter (fun j : Fin N => j < a) = Finset.Iio a := by ext j; simp
  rw [h, Fin.card_Iio]

/-- `Par` is `(-1)^a X^a + lower`: natDegree `≤ a` and coefficient `a` is `(-1)^a`. -/
theorem Pa_natDegree_le {N : ℕ} (π : Fin N → ℝ) (a : Fin N) : (Par π a).natDegree ≤ (a : ℕ) := by
  calc (Par π a).natDegree
      ≤ ∑ j ∈ Finset.univ.filter (fun j => j < a),
          (Polynomial.C (π j) - Polynomial.X).natDegree :=
        by unfold Par; exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j < a), 1 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = (a : ℕ) := by simp [Pa_card]

theorem Pa_coeff_self {N : ℕ} (π : Fin N → ℝ) (a : Fin N) : (Par π a).coeff (a : ℕ) = (-1) ^ (a : ℕ) := by
  have h : ∀ j ∈ Finset.univ.filter (fun j : Fin N => j < a),
      (Polynomial.C (π j) - Polynomial.X) = (-1 : Polynomial ℝ) * (Polynomial.X - Polynomial.C (π j)) := by
    intro j _; ring
  have hm : (Par π a) = (-1 : Polynomial ℝ) ^ (a : ℕ) *
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => j < a), (Polynomial.X - Polynomial.C (π j)) := by
    unfold Par
    rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Pa_card]
  have hmon : (∏ j ∈ Finset.univ.filter (fun j : Fin N => j < a),
      (Polynomial.X - Polynomial.C (π j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
  have hdeg : (∏ j ∈ Finset.univ.filter (fun j : Fin N => j < a),
      (Polynomial.X - Polynomial.C (π j))).natDegree = (a : ℕ) := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    simp [Pa_card]
  rw [hm, show ((-1 : Polynomial ℝ) ^ (a : ℕ)) = Polynomial.C ((-1 : ℝ) ^ (a : ℕ)) by simp,
    Polynomial.coeff_C_mul, ← hdeg, hmon.coeff_natDegree, mul_one]

theorem Pa_coeff_gt {N : ℕ} (π : Fin N → ℝ) (a : Fin N) (i : ℕ) (hi : (a : ℕ) < i) :
    (Par π a).coeff i = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (Pa_natDegree_le π a) hi)

/-- G3 part 2: the `B`-matrix `B̃_a(y_k) = Σ_{i<M} [p_a]_i y_k^{M-1-i}/(M-1-i)!` has
`det = (Π_a (-1)^a) (Π_k y_k^{M-N}) det[y_k^{N-1-i}] / Π_i (M-1-i)!`. -/
theorem detB {N : ℕ} (M : ℕ) (hNM : N ≤ M) (π : Fin N → ℝ) (y : Fin N → ℝ) :
    (Matrix.of fun a k : Fin N => ∑ i ∈ Finset.range M,
        (Par π a).coeff i * y k ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)).det =
      (∏ a : Fin N, (-1 : ℝ) ^ (a : ℕ)) * (∏ k, y k ^ (M - N)) *
        (Matrix.of fun i k : Fin N => y k ^ (N - 1 - (i : ℕ))).det /
          ∏ i : Fin N, ((M - 1 - (i : ℕ)).factorial : ℝ) := by
  set T : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun a i => (Par π a).coeff (i : ℕ) with hT
  set V : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i k =>
    ((((M - 1 - (i : ℕ)).factorial : ℝ))⁻¹) * (y k ^ (M - N) * y k ^ (N - 1 - (i : ℕ))) with hV
  have hmat : (Matrix.of fun a k : Fin N => ∑ i ∈ Finset.range M,
      (Par π a).coeff i * y k ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)) = T * V := by
    ext a k
    simp only [Matrix.of_apply, Matrix.mul_apply, hT, hV]
    have hsplit : Finset.range M = Finset.range N ∪ Finset.Ico N M := by
      simp only [Finset.range_eq_Ico]
      exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le N) hNM).symm
    rw [hsplit, Finset.sum_union (Finset.disjoint_left.2 (fun x h1 h2 => by
      simp only [Finset.mem_range] at h1; simp only [Finset.mem_Ico] at h2; omega))]
    have hz : ∑ i ∈ Finset.Ico N M,
        (Par π a).coeff i * y k ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Pa_coeff_gt π a i (by have := a.isLt; simp only [Finset.mem_Ico] at hi; omega)]
      simp
    rw [hz, add_zero, ← Fin.sum_univ_eq_sum_range (fun i =>
      (Par π a).coeff i * y k ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)) N]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := i.isLt
    rw [← pow_add, show M - N + (N - 1 - (i : ℕ)) = M - 1 - (i : ℕ) by omega]
    ring
  have hTdet : T.det = ∏ a : Fin N, (-1 : ℝ) ^ (a : ℕ) := by
    rw [Matrix.det_of_lowerTriangular T (fun a i (h : a < i) => by
      simp only [hT, Matrix.of_apply]; exact Pa_coeff_gt π a i h)]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    simp only [hT, Matrix.of_apply]
    exact Pa_coeff_self π a
  have hVdet : V.det = (∏ i : Fin N, ((((M - 1 - (i : ℕ)).factorial : ℝ))⁻¹)) *
      ((∏ k, y k ^ (M - N)) * (Matrix.of fun i k : Fin N => y k ^ (N - 1 - (i : ℕ))).det) := by
    have e1 : V = Matrix.of fun (i k : Fin N) => ((((M - 1 - (i : ℕ)).factorial : ℝ))⁻¹) *
        (Matrix.of fun i k : Fin N => y k ^ (M - N) * y k ^ (N - 1 - (i : ℕ))) i k := rfl
    rw [e1, Matrix.det_mul_column]
    congr 1
    have e2 : (Matrix.of fun i k : Fin N => y k ^ (M - N) * y k ^ (N - 1 - (i : ℕ))) =
        Matrix.of fun (i k : Fin N) => y k ^ (M - N) * (Matrix.of fun i k : Fin N => y k ^ (N - 1 - (i : ℕ))) i k := rfl
    rw [e2, Matrix.det_mul_row]
  rw [hmat, Matrix.det_mul, hTdet, hVdet, Finset.prod_inv_distrib]
  have hne : (∏ i : Fin N, ((M - 1 - (i : ℕ)).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  field_simp

theorem Pa_coeff {N : ℕ} (π : Fin N → ℝ) (a : Fin N) (i : ℕ) :
    (B4196D.Pa π a).coeff i = (((Par π a).coeff i : ℝ) : ℂ) := by
  have : B4196D.Pa π a = (Par π a).map (algebraMap ℝ ℂ) := by
    simp [B4196D.Pa, Par, Polynomial.map_prod]
  rw [this, Polynomial.coeff_map]; rfl

/-- real top-level row functions `B̃_a(y) = Σ_{i<M} [p_a]_i y^{M-1-i}/(M-1-i)!`. -/
noncomputable def Bt (M : ℕ) {N : ℕ} (π : Fin N → ℝ) (a : Fin N) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, (Par π a).coeff i * y ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)

theorem det_rev_vdm {N : ℕ} (y : Fin N → ℝ) :
    (Matrix.of fun i k : Fin N => y k ^ (N - 1 - (i : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ) * (Matrix.vandermonde y).det := by
  have : (Matrix.of fun i k : Fin N => y k ^ (N - 1 - (i : ℕ))) =
      (Matrix.vandermonde y).transpose.submatrix Fin.revPerm id := by
    ext i k
    simp [Matrix.vandermonde, Fin.val_rev]
    congr 1
    omega
  rw [this, Matrix.det_permute, Matrix.det_transpose]

/-- G3c: on the ordered cone, the telescoped density is a CONSTANT times `det[B̃_a(la_k)]`. -/
theorem Dk_eq_detBt {N : ℕ} (M : ℕ) (hNM : N ≤ M) (π : Fin N → ℝ) :
    ∃ κ : ℝ, ∀ la : Fin N → ℝ, StrictAnti la →
      Dk M N la = κ * (Matrix.of fun a k : Fin N => Bt M π a (la k)).det := by
  set s1 : ℝ := ∏ a : Fin N, (-1 : ℝ) ^ (a : ℕ)
  set ε : ℝ := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin N)) : ℤ) : ℝ)
  set P : ℝ := ∏ i : Fin N, ((M - 1 - (i : ℕ)).factorial : ℝ)
  have hs1 : s1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (by norm_num)
  have hε : ε ≠ 0 := by
    have : ε * ε = 1 := by
      simp only [ε]; rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    intro h; rw [h, zero_mul] at this; norm_num at this
  have hsg : sgn N ≠ 0 := by
    intro h; have := abs_sgn N; rw [h, abs_zero] at this; norm_num at this
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hPf := (Pf_pos M N).ne'
  refine ⟨P / (s1 * ε * sgn N * Pf M N), fun la hla => ?_⟩
  have hB := detB M hNM π la
  have hBt : (Matrix.of fun a k : Fin N => Bt M π a (la k)) = (Matrix.of fun a k : Fin N =>
      ∑ i ∈ Finset.range M, (Par π a).coeff i * la k ^ (M - 1 - i) / ((M - 1 - i).factorial : ℝ)) := rfl
  rw [hBt, hB, det_rev_vdm, det_vdm_strictAnti hla, Finset.prod_pow]
  unfold Dk
  field_simp
  ring

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

open Equiv in
/-- double permutation sum = `n! det A`. -/
theorem perm_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ σ : Perm (Fin n), ∑ τ : Perm (Fin n),
      ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) * ∏ k, A (σ k) (τ k) =
      (n.factorial : ℝ) * A.det := by
  have h1 : ∀ σ : Perm (Fin n), ∑ τ : Perm (Fin n),
      ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) * ∏ k, A (σ k) (τ k) = A.det := by
    intro σ
    rw [← Matrix.det_transpose, Matrix.det_apply', ← Equiv.sum_comp (Equiv.mulRight σ)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hs : ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign σ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
    have hp : ∏ k, A (σ k) ((ρ * σ) k) = ∏ i, A i (ρ i) :=
      Equiv.prod_comp σ (fun i => A i (ρ i))
    simp only [Equiv.coe_mulRight, Perm.sign_mul, Units.val_mul, Int.cast_mul, Matrix.transpose_apply]
    rw [hp]
    linear_combination (((Perm.sign ρ : ℤ) : ℝ) * ∏ i, A i (ρ i)) * hs
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

open Equiv in
theorem detdet_pointwise {n : ℕ} (f g : Fin n → ℝ → ℝ) (y : Fin n → ℝ) :
    (Matrix.of fun a k : Fin n => f a (y k)).det * (Matrix.of fun a k : Fin n => g a (y k)).det =
      ∑ σ : Perm (Fin n), ∑ τ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) *
        ∏ k, (f (σ k) (y k) * g (τ k) (y k)) := by
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.of_apply]
  ring

/-- ANDREIEF on a product set. -/
theorem andreief_cube {n : ℕ} (f g : Fin n → ℝ → ℝ) (I : Set ℝ)
    (hint : ∀ a b, IntegrableOn (fun u => f a u * g b u) I) :
    IntegrableOn (fun y : Fin n → ℝ => (Matrix.of fun a k : Fin n => f a (y k)).det *
        (Matrix.of fun a k : Fin n => g a (y k)).det) (Set.univ.pi fun _ : Fin n => I) ∧
    ∫ y in Set.univ.pi (fun _ : Fin n => I),
      (Matrix.of fun a k : Fin n => f a (y k)).det * (Matrix.of fun a k : Fin n => g a (y k)).det =
    (n.factorial : ℝ) * (Matrix.of fun a b : Fin n => ∫ u in I, f a u * g b u).det := by
  have hμ : (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi (fun _ : Fin n => I)) =
      Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict I) := by
    rw [MeasureTheory.volume_pi]
    exact Measure.restrict_pi_pi _ _
  have hI : ∀ (σ τ : Equiv.Perm (Fin n)),
      Integrable (fun y : Fin n → ℝ => ∏ k, (f (σ k) (y k) * g (τ k) (y k)))
        (Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict I)) :=
    fun σ τ => Integrable.fintype_prod (f := fun k t => f (σ k) t * g (τ k) t) (fun k => hint _ _)
  have hS : Integrable (fun y : Fin n → ℝ => ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) * ∏ k, (f (σ k) (y k) * g (τ k) (y k)))
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict I)) :=
    integrable_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => (hI σ τ).const_mul _
  simp_rw [IntegrableOn, detdet_pointwise f g]
  rw [hμ]
  refine ⟨hS, ?_⟩
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => (hI σ τ).const_mul _)),
    ← perm_double_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ (fun τ _ => (hI σ τ).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun k t => f (σ k) t * g (τ k) t)]
  rfl

theorem det_of_comp_perm {n : ℕ} (f : Fin n → ℝ → ℝ) (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (Matrix.of fun a k : Fin n => f a ((y ∘ σ) k)).det =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (Matrix.of fun a k : Fin n => f a (y k)).det := by
  have : (Matrix.of fun a k : Fin n => f a ((y ∘ σ) k)) =
      (Matrix.of fun a k : Fin n => f a (y k)).submatrix id σ := by
    ext a k; simp
  rw [this, Matrix.det_permute']

/-- ANDREIEF on the ordered cone: no factorial. -/
theorem andreief_cone {n : ℕ} (f g : Fin n → ℝ → ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (hint : ∀ a b, IntegrableOn (fun u => f a u * g b u) I) :
    ∫ y in SA n ∩ Set.univ.pi (fun _ : Fin n => I),
      (Matrix.of fun a k : Fin n => f a (y k)).det * (Matrix.of fun a k : Fin n => g a (y k)).det =
    (Matrix.of fun a b : Fin n => ∫ u in I, f a u * g b u).det := by
  obtain ⟨hint', hval⟩ := andreief_cube f g I hint
  have hC : MeasurableSet (Set.univ.pi fun _ : Fin n => I) := MeasurableSet.univ_pi fun _ => hI
  set h : (Fin n → ℝ) → ℝ := fun y => (Matrix.of fun a k : Fin n => f a (y k)).det *
      (Matrix.of fun a k : Fin n => g a (y k)).det with hh
  have hsym : ∀ σ : Equiv.Perm (Fin n), ∀ y,
      (Set.univ.pi fun _ : Fin n => I).indicator h (y ∘ σ) = (Set.univ.pi fun _ : Fin n => I).indicator h y := by
    intro σ y
    have hmem : (y ∘ σ) ∈ (Set.univ.pi fun _ : Fin n => I) ↔ y ∈ (Set.univ.pi fun _ : Fin n => I) := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
      exact ⟨fun H k => by simpa using H (σ.symm k), fun H k => H (σ k)⟩
    by_cases hy : y ∈ (Set.univ.pi fun _ : Fin n => I)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmem.2 hy)]
      simp only [hh, det_of_comp_perm]
      have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
      linear_combination ((Matrix.of fun a k : Fin n => f a (y k)).det *
        (Matrix.of fun a k : Fin n => g a (y k)).det) * hs
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun H => hy (hmem.1 H))]
  have hsy := integral_sym _ ((integrable_indicator_iff hC).2 hint') hsym
  rw [integral_indicator hC, hval, setIntegral_indicator hC] at hsy
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  exact (mul_left_cancel₀ hf hsy).symm

/-- G4e (generic): the det-side matrix in the `y = M u` variable, with the `α` rows expanded in the
moment rows `m_i` and the `β` rows written as `B_a`. -/
theorem DS_eq {N : ℕ} (M : ℕ) (hM : 0 < M) (q : ℝ) (β α B m : Fin N → ℝ → ℝ)
    (Cf : Matrix (Fin N) (Fin N) ℝ)
    (hBc : ∀ a, Continuous (B a)) (hmc : ∀ i, Continuous (m i))
    (hβ : ∀ a u, 0 < u → β a u = Real.exp (-(u * M * q)) * B a (u * M))
    (hα : ∀ b u, 0 < u → -(M : ℝ) * α b u = Real.exp (u * M * q) * ∑ i, Cf b i * m i (u * M))
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ, β a u * (-(M : ℝ) * α b u)).det =
      ((M : ℝ)⁻¹) ^ N * Cf.det *
        (Matrix.of fun a i : Fin N => ∫ y in Set.Ioc 0 (M * ξ), B a y * m i y).det := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hent : ∀ a b, ∫ u in Set.Ioc 0 ξ, β a u * (-(M : ℝ) * α b u) =
      (M : ℝ)⁻¹ * ∑ i, Cf b i * ∫ y in Set.Ioc 0 (M * ξ), B a y * m i y := by
    intro a b
    have h1 : ∫ u in Set.Ioc 0 ξ, β a u * (-(M : ℝ) * α b u) =
        ∫ u in Set.Ioc 0 ξ, ∑ i, Cf b i * (B a (u * M) * m i (u * M)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      rw [hβ a u hu.1, hα b u hu.1, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Real.exp (-(u * M * q)) * Real.exp (u * M * q) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (B a (u * M) * Cf b i * m i (u * M)) * this
    have hc : ∀ i, Continuous fun u : ℝ => B a (u * M) * m i (u * M) := fun i =>
      ((hBc a).comp (continuous_id.mul continuous_const)).mul ((hmc i).comp (continuous_id.mul continuous_const))
    rw [h1, integral_finset_sum _ (fun i _ => (((hc i).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self).const_mul _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    have hsc : ∫ u in Set.Ioc 0 ξ, B a (u * M) * m i (u * M) =
        (M : ℝ)⁻¹ * ∫ y in Set.Ioc 0 (M * ξ), B a y * m i y := by
      rw [← intervalIntegral.integral_of_le hξ, ← intervalIntegral.integral_of_le
        (mul_nonneg (Nat.cast_nonneg M) hξ)]
      rw [intervalIntegral.integral_comp_mul_right (fun y => B a y * m i y) hM']
      simp only [zero_mul, smul_eq_mul]
      rw [mul_comm ξ]
    rw [hsc]; ring
  have hmat : (Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ, β a u * (-(M : ℝ) * α b u)) =
      ((M : ℝ)⁻¹) • ((Matrix.of fun a i : Fin N => ∫ y in Set.Ioc 0 (M * ξ), B a y * m i y) * Cf.transpose) := by
    ext a b
    simp only [Matrix.of_apply, hent, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hmat, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin]
  ring

open Filter Topology in
/-- G4f: two functions that are both constant multiples of the same `X` and both tend to `1`
coincide (the constant-free normalisation). -/
theorem const_eq (P D X : ℝ → ℝ) (C1 C2 : ℝ) (hP : ∀ ξ, 0 ≤ ξ → P ξ = C1 * X ξ)
    (hD : ∀ ξ, 0 ≤ ξ → D ξ = C2 * X ξ) (hP1 : Tendsto P atTop (𝓝 1)) (hD1 : Tendsto D atTop (𝓝 1)) :
    ∀ ξ, 0 ≤ ξ → P ξ = D ξ := by
  have hev : ∀ᶠ ξ in atTop, (0 : ℝ) ≤ ξ := eventually_ge_atTop 0
  have hC2 : C2 ≠ 0 := by
    intro h
    have : Tendsto D atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with ξ hξ
      rw [hD ξ hξ, h, zero_mul]
    exact one_ne_zero (tendsto_nhds_unique hD1 this)
  have hX : Tendsto X atTop (𝓝 (C2⁻¹)) := by
    have : Tendsto (fun ξ => C2⁻¹ * D ξ) atTop (𝓝 (C2⁻¹ * 1)) := hD1.const_mul _
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hev] with ξ hξ
    rw [hD ξ hξ]; field_simp
  have hP' : Tendsto P atTop (𝓝 (C1 * C2⁻¹)) := by
    refine (hX.const_mul C1).congr' ?_
    filter_upwards [hev] with ξ hξ
    rw [hP ξ hξ]
  have h1 : C1 * C2⁻¹ = 1 := tendsto_nhds_unique hP' hP1
  have hC : C1 = C2 := by field_simp at h1; linarith
  intro ξ hξ
  rw [hP ξ hξ, hD ξ hξ, hC]

end B4196S

-- ===== GLUE (relay 10)
section Glue
open MeasureTheory Complex Metric Filter Topology

namespace B4196Z
open SpikedWishart.Separated.Lib.Weyl SWL302

/-- the common factor `X(L) = det[∫_{(0,L]} B̃_a m_i]`. -/
noncomputable def Xf (M : ℕ) {N : ℕ} (π : Fin N → ℝ) (c R : ℝ) (L : ℝ) : ℝ :=
  (Matrix.of fun a i : Fin N => ∫ y in Set.Ioc 0 L,
    B4196R.Bt M π a y * B4196G.row (B4196G.gm M π N i) c R y).det

theorem Bt_continuous (M : ℕ) {N : ℕ} (π : Fin N → ℝ) (a : Fin N) :
    Continuous (B4196R.Bt M π a) := by
  unfold B4196R.Bt
  fun_prop

theorem momdet_continuous (M : ℕ) {N : ℕ} (π : Fin N → ℝ) (c R : ℝ) (hR : 0 ≤ R)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) (n : ℕ) :
    Continuous (fun la : Fin n → ℝ => (B4196G.momMat M π c R n la).det) := by
  have h : Continuous (fun la : Fin n → ℝ => B4196G.momMat M π c R n la) := by
    refine continuous_matrix fun i k => ?_
    exact (B4196G.row_continuous _ c R hR (B4196G.gm_cont M π c R hπ n i)).comp (continuous_apply k)
  exact h.matrix_det

theorem Dk_nonneg (M k : ℕ) (la : Fin k → ℝ) (h : ∀ i, 0 ≤ la i) : 0 ≤ Dk M k la := by
  unfold Dk vdm
  exact div_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (pow_nonneg (Finset.prod_nonneg fun i _ => h i) _)) (Pf_pos M k).le

theorem Dk_continuous (M k : ℕ) : Continuous (fun la : Fin k → ℝ => Dk M k la) := by
  unfold Dk
  exact (continuous_vdm.mul ((continuous_finset_prod _ fun i _ => continuous_apply i).pow _)).div_const _

/-- MATRIX SIDE up to one constant: `P(λ₁ ≤ ξ) = C₁ · X(Mξ)`. -/
theorem matrix_side (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (π : Fin N → ℝ) (hπ0 : ∀ i, 0 < π i) (c R : ℝ) (hR : 0 ≤ R)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (c : ℂ) R) :
    ∃ C1 : ℝ, ∀ ξ : ℝ, 0 ≤ ξ →
      (SpikedWishart.FixedDim.sampleLaw M N).real
          {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ ξ} =
        C1 * Xf M π c R (M * ξ) := by
  haveI : NeZero N := ⟨by omega⟩
  let b : ℕ → ℝ := fun n => aπ π n + 1
  let F : (n : ℕ) → (Fin n → ℝ) → ℝ := fun n la => (B4196G.momMat M π c R n la).det
  have hF0 : ∀ x, F 0 x = 1 := fun x => Matrix.det_isEmpty
  have hFc : ∀ n, Continuous (F n) := fun n => momdet_continuous M π c R hR hπ n
  have hstep : ∀ n < N, ∃ C : ℝ, ∀ la : Fin (n + 1) → ℝ, StrictAnti la →
      ∫ μ in Set.univ.pi (fun k : Fin n => Set.Ioc (la k.succ) (la k.castSucc)),
        Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) * F n μ = C * F (n + 1) la := by
    intro n hn
    obtain ⟨C, hC⟩ := B4196G.gt_step M π c R hR hπ n hn (hπ0 _).ne'
    have hb : b n = π ⟨n, hn⟩ := by
      show aπ π n + 1 = π ⟨n, hn⟩
      simp [aπ, hn]
    exact ⟨C, fun la hla => by rw [hb]; exact hC la hla⟩
  obtain ⟨cN, hcN0, hcN⟩ := B4196W.gt_formula b F N hF0 hFc hstep N le_rfl
  obtain ⟨κ, hκ⟩ := B4196R.Dk_eq_detBt M hNM π
  refine ⟨(∏ i, π i ^ M) * (κ * cN), fun ξ hξ => ?_⟩
  have h5 := c2c hNM π hπ0 U ξ
  have h6 := chain_tele M (aπ π) b (fun n => by simp [b]) N
    (fun la : Fin N → ℝ => if la 0 ≤ (M : ℝ) * ξ then (1 : ENNReal) else 0)
  have hΦ : Measurable (fun la : Fin N → ℝ => ENNReal.ofReal (Dk M N la) *
      (if la 0 ≤ (M : ℝ) * ξ then (1 : ENNReal) else 0)) :=
    (ENNReal.measurable_ofReal.comp (Dk_continuous M N).measurable).mul
      (Measurable.ite (measurableSet_le (measurable_pi_apply 0) measurable_const)
        measurable_const measurable_const)
  have h7 := hcN _ hΦ
  beta_reduce at h7
  set S : Set (Fin N → ℝ) := B4196S.SA N ∩ Set.univ.pi (fun _ : Fin N => Set.Ioc 0 ((M : ℝ) * ξ)) with hSdef
  have hS : MeasurableSet S :=
    (B4196S.measurableSet_SA N).inter (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
  have hSG : ∀ la ∈ S, la ∈ Good N := fun la hla =>
    ⟨hla.1, fun k => (hla.2 k (Set.mem_univ _)).1⟩
  let f : (Fin N → ℝ) → ℝ := fun la => Dk M N la * (cN * F N la)
  have hf0 : ∀ la ∈ S, 0 ≤ f la := fun la hla =>
    mul_nonneg (Dk_nonneg M N la fun i => ((hSG la hla).2 i).le) (hcN0 la (hSG la hla))
  -- Step A: the lintegral over Good with the cut-off is the lintegral over S
  have hA : ∫⁻ la in Good N, ENNReal.ofReal (Dk M N la) *
      (if la 0 ≤ (M : ℝ) * ξ then (1 : ENNReal) else 0) * ENNReal.ofReal (cN * F N la) =
      ∫⁻ la in S, ENNReal.ofReal (f la) := by
    rw [← lintegral_indicator (B4196W.measurableSet_Good N), ← lintegral_indicator hS]
    refine lintegral_congr fun la => ?_
    by_cases hg : la ∈ Good N
    · by_cases h0 : la 0 ≤ (M : ℝ) * ξ
      · have hlS : la ∈ S := ⟨hg.1, fun k _ => ⟨hg.2 k, le_trans (hg.1.antitone (Fin.zero_le k)) h0⟩⟩
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem hlS]
        simp only [if_pos h0, mul_one, f]
        rw [ENNReal.ofReal_mul (Dk_nonneg M N la fun i => (hg.2 i).le)]
      · have hlS : la ∉ S := fun h => h0 (h.2 0 (Set.mem_univ _)).2
        rw [Set.indicator_of_mem hg, Set.indicator_of_notMem hlS]
        simp only [if_neg h0, mul_zero, zero_mul]
    · have hlS : la ∉ S := fun h => hg (hSG la h)
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hlS]
  -- Step B: integrability on S
  have hfc : Continuous f := (Dk_continuous M N).mul (continuous_const.mul (hFc N))
  have hint : IntegrableOn f S := by
    have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) ((M : ℝ) * ξ)) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hfc.continuousOn.integrableOn_compact hK).mono_set
      (fun la hla => fun k _ => Set.Ioc_subset_Icc_self (hla.2 k (Set.mem_univ _)))
  have hB : ∫⁻ la in S, ENNReal.ofReal (f la) = ENNReal.ofReal (∫ la in S, f la) :=
    (ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hf0))).symm
  have hI0 : 0 ≤ ∫ la in S, f la := setIntegral_nonneg hS hf0
  -- Step D: Dk = κ detB̃ on S
  have hD : ∫ la in S, f la = κ * cN *
      ∫ la in S, (Matrix.of fun a k : Fin N => B4196R.Bt M π a (la k)).det *
        (Matrix.of fun a k : Fin N => B4196G.row (B4196G.gm M π N a) c R (la k)).det := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hS fun la hla => ?_
    simp only [f, F]
    rw [hκ la hla.1]
    unfold B4196G.momMat
    ring
  have hE := B4196S.andreief_cone (B4196R.Bt M π) (fun i => B4196G.row (B4196G.gm M π N i) c R)
    (Set.Ioc 0 ((M : ℝ) * ξ)) measurableSet_Ioc (fun a i =>
      (((Bt_continuous M π a).mul (B4196G.row_continuous _ c R hR
        (B4196G.gm_cont M π c R hπ N i))).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
  have hX : ∫ la in S, (Matrix.of fun a k : Fin N => B4196R.Bt M π a (la k)).det *
        (Matrix.of fun a k : Fin N => B4196G.row (B4196G.gm M π N a) c R (la k)).det =
      Xf M π c R ((M : ℝ) * ξ) := hE
  rw [measureReal_def, h5, h6, h7, hA, hB]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hπ0 i).le M),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hπ0 i).le M),
    ENNReal.toReal_ofReal (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hπ0 i).le M) hI0), hD, hX]
  ring

/-- `β_a(u) = e^{-uMq} B̃_a(uM)` for `u > 0`. -/
theorem beta_Bt {N : ℕ} (M : ℕ) (hNM : N ≤ M) (π : Fin N → ℝ) (q cS ρS : ℝ)
    (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS) (a : Fin N) (u : ℝ) (hu : 0 < u) :
    B4196B.beta M π q cS ρS a u = Real.exp (-(u * M * q)) * B4196R.Bt M π a (u * M) := by
  apply Complex.ofReal_injective
  rw [B4196D.beta_explicit M hNM π q cS ρS hS0 a u hu.le, Complex.ofReal_mul (Real.exp _) _, Complex.ofReal_exp]
  unfold B4196R.Bt
  rw [Complex.ofReal_sum]
  congr 1
  · push_cast; ring_nf
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [B4196R.Pa_coeff]
    push_cast
    ring

/-- `det(∫_{(0,ξ]} β_a(-Mα_b)) → 1` as `ξ → ∞`. -/
theorem DS_tendsto {N : ℕ} (M : ℕ) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ ball (cΓ : ℂ) ρΓ) (hS0 : (0 : ℂ) ∈ ball (cS : ℂ) ρS) :
    Tendsto (fun ξ : ℝ => (Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ,
        B4196B.beta M π q cS ρS a u * (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)).det) atTop (𝓝 1) := by
  have hP : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, B4196B.Pz π z ≠ 0 := by
    intro z hz
    unfold B4196B.Pz
    rw [Finset.prod_ne_zero_iff]
    intro j _ h
    have h1 := hπ j
    rw [sub_eq_zero] at h
    rw [Metric.mem_sphere, ← h] at hz
    rw [Metric.mem_ball, hz] at h1
    exact lt_irrefl _ h1
  have h0 : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 := by
    intro w hw h
    rw [h, Metric.mem_sphere] at hw
    rw [Metric.mem_ball, hw] at hS0
    exact lt_irrefl _ hS0
  have hint : ∀ a b : Fin N, IntegrableOn (fun u => B4196B.beta M π q cS ρS a u *
      (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)) (Set.Ioi 0) := fun a b =>
    (B4196B.integrableOn_phi_psi M hM π q cΓ ρΓ cS ρS hρΓ hρS hsep hP h0 0 le_rfl b a).congr_fun
      (fun u _ => mul_comm _ _) measurableSet_Ioi
  have hent : ∀ a b : Fin N, Tendsto (fun ξ : ℝ => ∫ u in Set.Ioc 0 ξ,
      B4196B.beta M π q cS ρS a u * (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)) atTop
      (𝓝 (if a = b then 1 else 0)) := by
    intro a b
    rw [← B4196D.biorth M hM hNM π q cΓ ρΓ cS ρS hπ hS0 hsep a b]
    refine (intervalIntegral_tendsto_integral_Ioi 0 (hint a b) tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with ξ hξ
    exact intervalIntegral.integral_of_le hξ
  have hmat : Tendsto (fun ξ : ℝ => Matrix.of fun a b : Fin N => ∫ u in Set.Ioc 0 ξ,
      B4196B.beta M π q cS ρS a u * (-(M : ℝ) * B4196B.alpha M π q cΓ ρΓ b u)) atTop
      (𝓝 (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    have h1 : (1 : Matrix (Fin N) (Fin N) ℝ) = Matrix.of fun a b => if a = b then (1 : ℝ) else 0 := by
      ext a b; simp [Matrix.one_apply]
    rw [h1]
    exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hent a b
  have := (continuous_id.matrix_det.tendsto (1 : Matrix (Fin N) (Fin N) ℝ)).comp hmat
  have h2 : (id (1 : Matrix (Fin N) (Fin N) ℝ)).det = 1 := Matrix.det_one
  rw [h2] at this
  exact this

/-- the parent, assembled. -/
theorem main (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (q : ℝ) (hq0 : 0 < q) (hq : ∀ j, q < (ℓ j)⁻¹)
    (cΓ ρΓ : ℝ) (hΓ_encl : ∀ j, |(ℓ j)⁻¹ - cΓ| < ρΓ) (hΓ_right : q < cΓ - ρΓ)
    (cS ρS : ℝ) (hS_encl : |cS| < ρS) (hS_left : cS + ρS < q)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).real {G | SpikedWishart.SoftEdge.largestEig M U ℓ G ≤ ξ} =
      SpikedWishart.SoftEdge.fredholmDet
        (SpikedWishart.SoftEdge.kernelKMN M (fun j => (ℓ j)⁻¹) q cΓ ρΓ cS ρS) ξ := by
  have hM : 0 < M := by omega
  set π : Fin N → ℝ := fun j => (ℓ j)⁻¹ with hπdef
  have hπ0 : ∀ i, 0 < π i := fun i => inv_pos.2 (hℓ i)
  have hπ : ∀ j, ((π j : ℝ) : ℂ) ∈ Metric.ball (cΓ : ℂ) ρΓ := by
    intro j
    rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hΓ_encl j
  have hS0 : (0 : ℂ) ∈ Metric.ball (cS : ℂ) ρS := by
    rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact hS_encl
  have hρΓ : 0 ≤ ρΓ := (abs_nonneg _).trans (hΓ_encl ⟨0, by omega⟩).le
  have hρS : 0 ≤ ρS := (abs_nonneg _).trans hS_encl.le
  have hsep : cS + ρS < cΓ - ρΓ := by linarith
  have hinv : (fun i => (π i)⁻¹) = ℓ := funext fun i => inv_inv _
  obtain ⟨C1, hC1⟩ := matrix_side M N hN hNM U π hπ0 cΓ ρΓ hρΓ hπ
  rw [hinv] at hC1
  obtain ⟨Cf, hCf⟩ := B4196E.alpha_expand M π q cΓ ρΓ hρΓ hπ
  have hDS : ∀ ξ : ℝ, 0 ≤ ξ → SpikedWishart.SoftEdge.fredholmDet
        (SpikedWishart.SoftEdge.kernelKMN M π q cΓ ρΓ cS ρS) ξ =
      ((M : ℝ)⁻¹ ^ N * Cf.det) * Xf M π cΓ ρΓ (M * ξ) := by
    intro ξ hξ
    rw [B4196.det_side M N hN hNM ℓ q cΓ ρΓ hΓ_encl hΓ_right cS ρS hS_encl hS_left ξ hξ]
    exact B4196S.DS_eq M hM q (B4196B.beta M π q cS ρS) (B4196B.alpha M π q cΓ ρΓ)
      (B4196R.Bt M π) (fun i => B4196G.row (B4196G.gm M π N i) cΓ ρΓ) Cf
      (fun a => Bt_continuous M π a)
      (fun i => B4196G.row_continuous _ cΓ ρΓ hρΓ (B4196G.gm_cont M π cΓ ρΓ hπ N i))
      (fun a u hu => beta_Bt M hNM π q cS ρS hS0 a u hu)
      (fun b u _ => hCf b u) ξ hξ
  have hP1 : Tendsto (fun ξ : ℝ => (SpikedWishart.SoftEdge.sampleLaw M N).real
      {G | SpikedWishart.SoftEdge.largestEig M U ℓ G ≤ ξ}) atTop (𝓝 1) := by
    haveI : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M N) := by
      show IsProbabilityMeasure (SpikedWishart.FixedDim.sampleLaw M N)
      infer_instance
    have hmono : Monotone (fun ξ : ℝ => {G | SpikedWishart.SoftEdge.largestEig M U ℓ G ≤ ξ}) :=
      fun a b hab G hG => le_trans hG hab
    have h1 := tendsto_measure_iUnion_atTop (μ := SpikedWishart.SoftEdge.sampleLaw M N) hmono
    have hU : (⋃ ξ : ℝ, {G | SpikedWishart.SoftEdge.largestEig M U ℓ G ≤ ξ}) = Set.univ :=
      Set.eq_univ_of_forall fun G => by
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨_, le_rfl⟩
    rw [hU, measure_univ] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    rw [ENNReal.toReal_one] at h2
    simp only [measureReal_def]
    exact h2
  have hD1 : Tendsto (fun ξ : ℝ => SpikedWishart.SoftEdge.fredholmDet
      (SpikedWishart.SoftEdge.kernelKMN M π q cΓ ρΓ cS ρS) ξ) atTop (𝓝 1) := by
    refine (DS_tendsto M hM hNM π q cΓ ρΓ cS ρS hρΓ hρS hsep hπ hS0).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with ξ hξ
    exact (B4196.det_side M N hN hNM ℓ q cΓ ρΓ hΓ_encl hΓ_right cS ρS hS_encl hS_left ξ hξ).symm
  have hMS : ∀ ξ : ℝ, 0 ≤ ξ → (SpikedWishart.SoftEdge.sampleLaw M N).real
      {G | SpikedWishart.SoftEdge.largestEig M U ℓ G ≤ ξ} = C1 * Xf M π cΓ ρΓ (M * ξ) :=
    fun ξ hξ => hC1 ξ hξ
  exact B4196S.const_eq _ _ (fun ξ => Xf M π cΓ ρΓ (M * ξ)) C1 _ hMS hDS hP1 hD1 ξ hξ

end B4196Z
end Glue

open SpikedWishart.SoftEdge MeasureTheory in
theorem solution (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (q : ℝ) (hq0 : 0 < q) (hq : ∀ j, q < (ℓ j)⁻¹)
    (cΓ ρΓ : ℝ) (hΓ_encl : ∀ j, |(ℓ j)⁻¹ - cΓ| < ρΓ) (hΓ_right : q < cΓ - ρΓ)
    (cS ρS : ℝ) (hS_encl : |cS| < ρS) (hS_left : cS + ρS < q)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (sampleLaw M N).real {G | largestEig M U ℓ G ≤ ξ} =
      fredholmDet (kernelKMN M (fun j => (ℓ j)⁻¹) q cΓ ρΓ cS ρS) ξ := by
  exact B4196Z.main M N hN hNM U ℓ hℓ q hq0 hq cΓ ρΓ hΓ_encl hΓ_right cS ρS hS_encl hS_left ξ hξ
