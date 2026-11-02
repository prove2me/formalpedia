-- Prove2me | solution 1 for SpikedWishart.Separated.gue_top_eigenvalue_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:08:04.688193+00:00
-- url     : https://prove2.me/submissions/bd6297a8-cc1a-4336-8ce8-adee9aea323b

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE

set_option autoImplicit false
set_option linter.all false

open Filter Topology MeasureTheory Matrix
open scoped ComplexOrder
open Filter Topology MeasureTheory
open Filter Topology MeasureTheory Matrix Polynomial
open Filter Topology MeasureTheory Matrix Complex ProbabilityTheory
open Filter Topology MeasureTheory Matrix Polynomial ProbabilityTheory Complex

namespace SpikedWishart.Separated.Lib

-- ===== from ChildStatements.lean =====
section

/-- Q4 (BBP Def. 1.2 / (26)-(28), Weyl integration formula for the GUE): for the `k × k` GUE
`H = (Z + Zᴴ)/√2` built from i.i.d. standard complex Gaussians (diagonal `N(0,1)`, off-diagonal
`E|H_ij|² = 1`, density `∝ exp(-tr H²/2)`), `P(λ_max(H) ≤ x) = G k x`; `λ_max ≤ x` is written as
`x·1 - H ⪰ 0`. -/
def Q4_gueMax : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x

end

-- ===== from GCont2.lean =====
section

open Set

theorem pair_bound (D a b : ℝ) (hD : 0 < D) (s : ℝ) (hs : a ^ 2 + b ^ 2 ≤ s) :
    |a - b| ^ 2 ≤ (2 * D + 1) * Real.exp (s / D) := by
  have h1 : |a - b| ^ 2 ≤ 2 * s := by
    rw [sq_abs]; nlinarith [sq_nonneg (a + b)]
  have h2 : s / D + 1 ≤ Real.exp (s / D) := Real.add_one_le_exp _
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h3 : 2 * s = 2 * D * (s / D) := by field_simp
  have h4 : 0 ≤ s / D := div_nonneg hs0 hD.le
  have h5 : 1 ≤ Real.exp (s / D) := Real.one_le_exp h4
  have h6 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * D)
  nlinarith

theorem two_le_sum {k : ℕ} (ξ : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j) :
    ξ i ^ 2 + ξ j ^ 2 ≤ ∑ l, ξ l ^ 2 := by
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => ξ l ^ 2)
    (Finset.subset_univ {i, j}) (fun l _ _ => sq_nonneg (ξ l))
  rwa [Finset.sum_pair hij] at this

theorem pairProd_le {k : ℕ} (ξ : Fin k → ℝ) (D : ℝ) (hD : 0 < D) :
    (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, |ξ i - ξ j| ^ 2) ≤
      ((2 * D + 1) * Real.exp ((∑ l, ξ l ^ 2) / D)) ^ (k * k) := by
  set c := (2 * D + 1) * Real.exp ((∑ l, ξ l ^ 2) / D) with hc
  have hc1 : 1 ≤ c := by
    have : 1 ≤ Real.exp ((∑ l, ξ l ^ 2) / D) :=
      Real.one_le_exp (div_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _) hD.le)
    nlinarith
  calc (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, |ξ i - ξ j| ^ 2)
      ≤ ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, c := by
        apply Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by positivity)
        intro i _
        apply Finset.prod_le_prod (fun j _ => by positivity)
        intro j hj
        have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
        exact pair_bound D _ _ hD _ (two_le_sum ξ i j hij)
    _ ≤ ∏ _i : Fin k, c ^ k := by
        apply Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by linarith)
        intro i _
        rw [Finset.prod_const]
        exact pow_le_pow_right₀ hc1 (by simpa using Finset.card_le_univ (Finset.Ioi i))
    _ = c ^ (k * k) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem gueWeight_nonneg (k : ℕ) (ξ : Fin k → ℝ) : 0 ≤ gueWeight k ξ := by
  unfold gueWeight; positivity

theorem gueWeight_le (k : ℕ) (ξ : Fin k → ℝ) :
    gueWeight k ξ ≤ (2 * (4 * (k : ℝ) * k + 4) + 1) ^ (k * k) *
      ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2) := by
  have hD0 : (0 : ℝ) < 4 * (k : ℝ) * k + 4 := by positivity
  have hs0 : 0 ≤ ∑ l, ξ l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hB : ∏ i : Fin k, Real.exp (-(1 / 2) * ξ i ^ 2) = Real.exp (-(1 / 2) * ∑ l, ξ l ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  have hH : ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2) = Real.exp (-(1 / 4) * ∑ l, ξ l ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  unfold gueWeight
  rw [hB, hH]
  have hA := pairProd_le ξ (4 * (k : ℝ) * k + 4) hD0
  set s := ∑ l, ξ l ^ 2 with hs
  set D : ℝ := 4 * (k : ℝ) * k + 4 with hD
  have hkey : ((k * k : ℕ) : ℝ) * (s / D) ≤ s / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hD0 (by norm_num)]
    push_cast
    nlinarith
  calc _ ≤ ((2 * D + 1) * Real.exp (s / D)) ^ (k * k) * Real.exp (-(1 / 2) * s) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = (2 * D + 1) ^ (k * k) * Real.exp (((k * k : ℕ) : ℝ) * (s / D) + (-(1 / 2) * s)) := by
        rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]; ring
    _ ≤ (2 * D + 1) ^ (k * k) * Real.exp (-(1 / 4) * s) := by
        gcongr
        linarith

theorem gueWeight_continuous (k : ℕ) : Continuous (gueWeight k) := by
  unfold gueWeight
  refine Continuous.mul ?_ ?_
  · exact continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
      (((continuous_apply i).sub (continuous_apply j)).abs).pow 2
  · exact continuous_finsetProd _ fun i _ =>
      Real.continuous_exp.comp (continuous_const.mul ((continuous_apply i).pow 2))

theorem gueWeight_integrable (k : ℕ) : Integrable (gueWeight k) := by
  have hdom : Integrable (fun ξ : Fin k → ℝ => (2 * (4 * (k : ℝ) * k + 4) + 1) ^ (k * k) *
      ∏ i : Fin k, Real.exp (-(1 / 4) * ξ i ^ 2)) := by
    refine Integrable.const_mul ?_ _
    exact Integrable.fintype_prod (f := fun _ t => Real.exp (-(1 / 4) * t ^ 2))
      (fun _ => integrable_exp_neg_mul_sq (by norm_num))
  refine hdom.mono' (gueWeight_continuous k).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gueWeight_nonneg k ξ)]
  exact gueWeight_le k ξ

theorem gueWeight_pos_at (k : ℕ) : 0 < gueWeight k (fun i : Fin k => ((i : ℕ) : ℝ)) := by
  unfold gueWeight
  refine mul_pos (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_)
    (Finset.prod_pos fun i _ => Real.exp_pos _)
  have hij' : i < j := Finset.mem_Ioi.mp hj
  have hij : (i : ℕ) < j := hij'
  have : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≠ 0 := by
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  positivity

theorem Z_pos (k : ℕ) : 0 < Z k := by
  unfold Z
  rw [integral_pos_iff_support_of_nonneg (fun ξ => gueWeight_nonneg k ξ) (gueWeight_integrable k)]
  have hopen : IsOpen (Function.support (gueWeight k)) := (gueWeight_continuous k).isOpen_support
  exact hopen.measure_pos _ ⟨_, (gueWeight_pos_at k).ne'⟩

end

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

theorem trace_arrowR_sq {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) :
    (arrowR mu b c * arrowR mu b c).trace = ∑ i, mu i ^ 2 + 2 * ∑ i, b i ^ 2 + c ^ 2 := by
  simp only [Matrix.trace, diag_apply, mul_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, arrowR_cc, arrowR_cl, arrowR_lc, arrowR_ll, diagonal_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, if_true]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', mem_univ, if_true]
  ring_nf

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

theorem sum_sq_la {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    ∑ j, la j ^ 2 = ∑ i, mu i ^ 2 + 2 * ∑ i, wv mu la i + cv mu la ^ 2 := by
  obtain ⟨U, hU, hsim⟩ := arrowC_similar h
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff'.mp hU)
  have htr : (arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) *
      arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la)).trace =
      (U * diagonal (fun j => (la j : ℂ)) * star U * (U * diagonal (fun j => (la j : ℂ)) * star U)).trace := by
    rw [hsim]
  have h1 : (U * diagonal (fun j => (la j : ℂ)) * star U * (U * diagonal (fun j => (la j : ℂ)) * star U)).trace
      = ∑ j, ((la j ^ 2 : ℝ) : ℂ) := by
    rw [show U * diagonal (fun j => (la j : ℂ)) * star U * (U * diagonal (fun j => (la j : ℂ)) * star U)
        = U * (diagonal (fun j => (la j : ℂ)) * (star U * U) * diagonal (fun j => (la j : ℂ))) * star U by
        simp only [mul_assoc], hUU, mul_one, trace_mul_cycle, hUU, one_mul, diagonal_mul_diagonal,
      trace_diagonal]
    simp [sq]
  have h2 : (arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) *
      arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la)).trace =
      (((arrowR mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) *
        arrowR mu (fun i => Real.sqrt (wv mu la i)) (cv mu la)).trace : ℝ) : ℂ) := by
    rw [arrowC, show (fun x : ℝ => (x : ℂ)) = ⇑Complex.ofRealHom from rfl, ← Matrix.map_mul]
    rw [Matrix.trace, Matrix.trace, Complex.ofReal_sum]
    rfl
  rw [h1, h2, trace_arrowR_sq] at htr
  have hw : ∀ i, Real.sqrt (wv mu la i) ^ 2 = wv mu la i := fun i => Real.sq_sqrt (wv_pos h i).le
  simp only [hw] at htr
  rw [← Complex.ofReal_sum] at htr
  exact (Complex.ofReal_injective htr).symm

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

theorem charFun_cg (t : ℂ) :
    charFun SpikedWishart.SoftEdge.stdComplexGaussian t = cexp (-(((t.re ^ 2 + t.im ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [charFun_apply, ← cg_char t.re t.im]
  congr 1; funext z; congr 2
  simp [Complex.inner]; try ring

/-- `√2 Re g ~ N(0,1)` for a standard complex Gaussian `g`. -/
theorem map_re_cg :
    SpikedWishart.SoftEdge.stdComplexGaussian.map (fun z => Real.sqrt 2 * z.re) = gaussianReal 0 1 := by
  have := isProb_cg
  have : IsProbabilityMeasure
      (SpikedWishart.SoftEdge.stdComplexGaussian.map (fun z => Real.sqrt 2 * z.re)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_gaussianReal, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have h := cg_char (t * Real.sqrt 2) 0
  have hfun : (fun z : ℂ => cexp (↑t * ↑(Real.sqrt 2 * z.re) * I)) =
      fun z : ℂ => cexp ((((t * Real.sqrt 2) * z.re + 0 * z.im : ℝ) : ℂ) * I) := by
    funext z; congr 1; push_cast; ring
  rw [hfun, h]
  congr 1
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  rw [mul_pow, show ((Real.sqrt 2 : ℂ)) ^ 2 = ((Real.sqrt 2 ^ 2 : ℝ) : ℂ) by push_cast; ring, h2]
  try push_cast
  try ring

/-- The map `(u, v) ↦ (u + conj v)/√2`. -/
noncomputable def rot (p : ℂ × ℂ) : ℂ := ((Real.sqrt 2)⁻¹ : ℝ) • (p.1 + star p.2)

theorem measurable_rot : Measurable rot := by unfold rot; fun_prop

/-- Rotation invariance: `(u + conj v)/√2` is again a standard complex Gaussian. -/
theorem map_rot_cg :
    (SpikedWishart.SoftEdge.stdComplexGaussian.prod SpikedWishart.SoftEdge.stdComplexGaussian).map rot =
      SpikedWishart.SoftEdge.stdComplexGaussian := by
  have := isProb_cg
  have : IsProbabilityMeasure
      ((SpikedWishart.SoftEdge.stdComplexGaussian.prod SpikedWishart.SoftEdge.stdComplexGaussian).map rot) :=
    Measure.isProbabilityMeasure_map measurable_rot.aemeasurable
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_cg, charFun_apply, integral_map measurable_rot.aemeasurable (by fun_prop)]
  set a := t.re / Real.sqrt 2
  set b := t.im / Real.sqrt 2
  have hkey : ∀ p : ℂ × ℂ, cexp (((inner ℝ (rot p) t : ℝ) : ℂ) * I) =
      cexp (((a * p.1.re + b * p.1.im : ℝ) : ℂ) * I) * cexp (((a * p.2.re + (-b) * p.2.im : ℝ) : ℂ) * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) * (1 / 2) := by
      apply inv_eq_of_mul_eq_one_right; rw [← mul_assoc, hs2]; norm_num
    simp only [rot, Complex.inner, a, b]
    simp
    push_cast
    simp only [div_eq_mul_inv, hinv]
    ring
  simp_rw [hkey]
  rw [integral_prod_mul (fun u : ℂ => cexp (((a * u.re + b * u.im : ℝ) : ℂ) * I))
    (fun v : ℂ => cexp (((a * v.re + (-b) * v.im : ℝ) : ℂ) * I)), cg_char, cg_char, ← Complex.exp_add]
  congr 1
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : a ^ 2 = t.re ^ 2 / 2 := by simp only [a]; rw [div_pow, h2]
  have hb : b ^ 2 = t.im ^ 2 / 2 := by simp only [b]; rw [div_pow, h2]
  have hb' : (-b) ^ 2 = t.im ^ 2 / 2 := by rw [neg_sq, hb]
  rw [ha, hb, hb']
  push_cast
  ring

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

theorem sqrt2_inv_c : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) * (1 / 2) := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  apply inv_eq_of_mul_eq_one_right; rw [← mul_assoc, hs2]; norm_num

/-- Bordering decomposition of the GUE matrix. -/
theorem gueMat_succ {n : ℕ} (Z : Fin (n + 1) → Fin (n + 1) → ℂ) :
    gueMat Z = blk (gueMat (fun i j : Fin n => Z i.castSucc j.castSucc))
      (fun i => rot (Z i.castSucc (Fin.last n), Z (Fin.last n) i.castSucc))
      (Real.sqrt 2 * (Z (Fin.last n) (Fin.last n)).re) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [blk_ll]
    simp only [gueMat, Matrix.smul_apply, Matrix.add_apply, of_apply, conjTranspose_apply, smul_eq_mul]
    rw [show star (Z (Fin.last n) (Fin.last n)) = (starRingEnd ℂ) (Z (Fin.last n) (Fin.last n)) from rfl,
      Complex.add_conj, sqrt2_inv_c]
    push_cast; ring
  · rw [blk_lc]
    simp only [gueMat, Matrix.smul_apply, Matrix.add_apply, of_apply, conjTranspose_apply, smul_eq_mul, rot]
    rw [Complex.real_smul]
    simp only [star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    push_cast; ring
  · rw [blk_cl]
    simp only [gueMat, Matrix.smul_apply, Matrix.add_apply, of_apply, conjTranspose_apply, smul_eq_mul, rot]
    rw [Complex.real_smul]
    push_cast; ring
  · rw [blk_cc]
    simp [gueMat, conjTranspose_apply]

/-- Splitting off the last coordinate of an i.i.d. vector. -/
theorem mp_lastSplit {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (fun r : Fin (n + 1) → X => (r (Fin.last n), fun j : Fin n => r (Fin.castSucc j)))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  convert h using 1
  funext r
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.succAbove_last]
  try rfl

/-- The bordering split `Z ↦ (Z₁₁, (u, (z, v)))` of the Gaussian array. -/
theorem mp_D (n : ℕ) :
    MeasurePreserving (fun Z : Fin (n + 1) → Fin (n + 1) → ℂ =>
      ((fun i j : Fin n => Z i.castSucc j.castSucc),
        ((fun i : Fin n => Z i.castSucc (Fin.last n)),
          (Z (Fin.last n) (Fin.last n), fun j : Fin n => Z (Fin.last n) j.castSucc))))
      (SpikedWishart.SoftEdge.sampleLaw (n + 1) (n + 1))
      ((SpikedWishart.SoftEdge.sampleLaw n n).prod
        ((Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod
          (SpikedWishart.SoftEdge.stdComplexGaussian.prod
            (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)))) := by
  have := isProb_cg
  have h1 := mp_lastSplit (Measure.pi fun _ : Fin (n + 1) => SpikedWishart.SoftEdge.stdComplexGaussian) n
  have hrow := mp_lastSplit SpikedWishart.SoftEdge.stdComplexGaussian n
  have h2 := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin (n + 1) =>
      SpikedWishart.SoftEdge.stdComplexGaussian)
    (fun _ => SpikedWishart.SoftEdge.stdComplexGaussian.prod
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)) (fun _ => hrow)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin n → ℂ) (Fin n)
    (fun _ => SpikedWishart.SoftEdge.stdComplexGaussian)
    (fun _ => Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
  have hW := h3.comp h2
  have h4 := (hrow.prod hW).comp h1
  have h5 := (Measure.measurePreserving_swap).comp h4
  have h6 := ((Measure.measurePreserving_swap).prod (MeasurePreserving.id _)).comp h5
  have h7 := (measurePreserving_prodAssoc _ _ _).comp h6
  exact h7

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

/-- Phase reduction: the bordered diagonal matrix is unitarily similar to the real arrow matrix. -/
theorem blk_diag_similar {n : ℕ} (mu : Fin n → ℝ) (b : Fin n → ℂ) (c : ℝ) :
    ∃ U ∈ unitaryGroup (Fin (n + 1)) ℂ,
      blk (diagonal fun i => (mu i : ℂ)) b c = U * arrowC mu (fun i => ‖b i‖) c * star U := by
  set d : Fin (n + 1) → ℂ := Fin.snoc (α := fun _ => ℂ) (fun i => ph (b i)) 1 with hd
  have hdd : ∀ p, d p * star (d p) = 1 := by
    intro p
    refine Fin.lastCases ?_ (fun i => ?_) p
    · simp [hd]
    · simp only [hd, Fin.snoc_castSucc]; exact ph_mul_star _
  refine ⟨diagonal d, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext p
    exact hdd p
  · rw [star_eq_conjTranspose, diagonal_conjTranspose]
    ext p q
    rw [mul_diagonal, diagonal_mul]
    simp only [Pi.star_apply]
    refine Fin.lastCases ?_ (fun i => ?_) p <;> refine Fin.lastCases ?_ (fun j => ?_) q
    · rw [blk_ll]
      simp [hd, arrowC, arrowR_ll]
    · rw [blk_lc]
      simp only [hd, Fin.snoc_last, Fin.snoc_castSucc, arrowC, map_apply, arrowR_lc, one_mul]
      conv_lhs => rw [← ph_mul_norm (b j)]
      simp [star_mul', mul_comm]
    · rw [blk_cl]
      simp only [hd, Fin.snoc_last, Fin.snoc_castSucc, arrowC, map_apply, arrowR_cl, star_one, mul_one]
      exact (ph_mul_norm (b i)).symm
    · rw [blk_cc]
      simp only [hd, Fin.snoc_castSucc, arrowC, map_apply, arrowR_cc]
      by_cases hij : i = j
      · subst hij
        simp only [diagonal_apply_eq]
        rw [mul_comm (ph (b i)), mul_assoc, ph_mul_star, mul_one]
      · simp [diagonal_apply_ne _ hij]

end Weyl

end

-- ===== from W5d.lean =====
section

namespace Weyl

/-- `(u, v) ↦ (u + conj v)/√2` coordinatewise maps two Gaussian vectors to one. -/
theorem mp_rotvec (n : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℂ) × (Fin n → ℂ) => fun i => rot (p.1 i, p.2 i))
      ((Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod
        (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian))
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) := by
  have := isProb_cg
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ ℂ (Fin n)
    (fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) (fun _ => SpikedWishart.SoftEdge.stdComplexGaussian)
  have hsf : ∀ _ : Fin n, SigmaFinite ((SpikedWishart.SoftEdge.stdComplexGaussian.prod
      SpikedWishart.SoftEdge.stdComplexGaussian).map rot) := fun _ => by rw [map_rot_cg]; infer_instance
  have hmap : MeasurePreserving (fun x : Fin n → ℂ × ℂ => fun i => rot (x i))
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian.prod
        SpikedWishart.SoftEdge.stdComplexGaussian)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) := by
    refine ⟨measurable_pi_lambda _ (fun i => measurable_rot.comp (measurable_pi_apply i)), ?_⟩
    rw [Measure.pi_map_pi (fun _ => measurable_rot.aemeasurable)]
    simp only [map_rot_cg]
  exact hmap.comp h3.symm

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

/-- Density form of `Exp(1)^n ⊗ N(0,1)` on `ℝ^(n+1)`. -/
theorem lintegral_exp_gauss {n : ℕ} (Φ : (Fin n → ℝ) × ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ p, Φ p ∂((Measure.pi fun _ : Fin n => exp1).prod (gaussianReal 0 1)) =
      ∫⁻ y : Fin (n + 1) → ℝ, Φ (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * gaussianPDFReal 0 1 (y (Fin.last n))) := by
  have hDw : Measurable (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) :=
    Finset.measurable_prod _ (fun i _ => measurable_dexp.ennreal_ofReal.comp (measurable_pi_apply i))
  have hM : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      ((fun p : (Fin n → ℝ) × ℝ => (∏ i, ENNReal.ofReal (dexp (p.1 i))) * gaussianPDF 0 1 p.2) * Φ) p) :=
    ((hDw.comp measurable_fst).mul ((measurable_gaussianPDF 0 1).comp measurable_snd)).mul hΦ
  rw [pi_exp1, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity hDw (measurable_gaussianPDF 0 1),
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun z : (Fin n → ℝ) × ℝ => (∏ i, ENNReal.ofReal (dexp (z.1 i))) * gaussianPDF 0 1 z.2)
      ((hDw.comp measurable_fst).mul ((measurable_gaussianPDF 0 1).comp measurable_snd)) hΦ,
    ← lintegral_prod_swap]
  have h := mp_lastSplit (volume : Measure ℝ) n
  refine Eq.trans (h.lintegral_comp (hM.comp measurable_swap)).symm ?_
  refine lintegral_congr (fun y => ?_)
  simp only [Pi.mul_apply, Function.comp_apply, Prod.swap, gaussianPDF]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => dexp_nonneg _)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => dexp_nonneg _)]
  rw [show Fin.init y = fun j => y j.castSucc from rfl]
  ring

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

/-- The bordering data `(b, c) = ((u + conj v)/√2, √2 Re z)`. -/
theorem mp_bc (n : ℕ) :
    MeasurePreserving (fun q : (Fin n → ℂ) × (ℂ × (Fin n → ℂ)) =>
        ((fun i => rot (q.1 i, q.2.2 i)), Real.sqrt 2 * q.2.1.re))
      ((Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod
        (SpikedWishart.SoftEdge.stdComplexGaussian.prod
          (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)))
      ((Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod (gaussianReal 0 1)) := by
  have := isProb_cg
  have s1 := (MeasurePreserving.id (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)).prod
    (Measure.measurePreserving_swap (μ := SpikedWishart.SoftEdge.stdComplexGaussian)
      (ν := Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian))
  have s2 := (measurePreserving_prodAssoc (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
    (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
    SpikedWishart.SoftEdge.stdComplexGaussian).symm
  have s3 := (mp_rotvec n).prod (MeasurePreserving.id SpikedWishart.SoftEdge.stdComplexGaussian)
  have hre : MeasurePreserving (fun z : ℂ => Real.sqrt 2 * z.re) SpikedWishart.SoftEdge.stdComplexGaussian
      (gaussianReal 0 1) := ⟨by fun_prop, map_re_cg⟩
  have s4 := (MeasurePreserving.id (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)).prod hre
  exact s4.comp (s3.comp (s2.comp s1))

/-- The law of the border `(b, c)`. -/
noncomputable def nu (n : ℕ) : Measure ((Fin n → ℂ) × ℝ) :=
  (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian).prod (gaussianReal 0 1)

/-- Averaging `F` over the random border of `K`. -/
noncomputable def hfun {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal)
    (K : Matrix (Fin n) (Fin n) ℂ) : ENNReal :=
  ∫⁻ p, F (blk K p.1 p.2) ∂(nu n)

theorem continuous_blk {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × ((Fin n → ℂ) × ℝ) => blk x.1 x.2.1 x.2.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp only [blk_ll]; fun_prop
  · simp only [blk_lc]; fun_prop
  · simp only [blk_cl]; fun_prop
  · simp only [blk_cc]; fun_prop

theorem measurable_hfun {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal) (hFm : Measurable F) :
    Measurable (hfun F) := by
  have hm : Measurable (fun x : Matrix (Fin n) (Fin n) ℂ × ((Fin n → ℂ) × ℝ) => F (blk x.1 x.2.1 x.2.2)) :=
    hFm.comp continuous_blk.measurable
  have := isProb_cg
  haveI : SFinite (nu n) := by unfold nu; infer_instance
  exact hm.lintegral_prod_right'

theorem ofOne : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (((1 : ℝ)) : ℂ)) = 1 := by
  ext i j
  simp [Matrix.one_apply, Subsingleton.elim i j]

theorem blk_conj {n : ℕ} (U K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) :
    blk (U * K * star U) (U *ᵥ b) c = blk U 0 1 * blk K b c * star (blk U 0 1) := by
  unfold blk
  simp only [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
    fromBlocks_conjTranspose, fromBlocks_multiply, ofOne, Pi.zero_apply, star_zero, of_zero_col,
    of_zero_row, conjTranspose_zero, conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | (ext i j; simp [mul_apply, mulVec, dotProduct, conjTranspose_apply, star_sum, mul_comm])

theorem blk_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    blk U 0 1 ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  unfold blk
  simp only [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
    fromBlocks_conjTranspose, fromBlocks_multiply, ofOne, Pi.zero_apply, star_zero, of_zero_col,
    of_zero_row, conjTranspose_zero, conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one, hUU, fromBlocks_one, submatrix_one_equiv]

theorem hfun_inv {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal) (hFm : Measurable F)
    (hF : ∀ U ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ A, F (U * A * star U) = F A)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hfun F (U * K * star U) = hfun F K := by
  have := isProb_cg
  have hmp : MeasurePreserving (fun p : (Fin n → ℂ) × ℝ => (U *ᵥ p.1, p.2)) (nu n) (nu n) :=
    (piCG_unitary U hU).prod (MeasurePreserving.id _)
  have hf : Measurable (fun p : (Fin n → ℂ) × ℝ => F (blk (U * K * star U) p.1 p.2)) :=
    hFm.comp (continuous_blk.comp (continuous_const.prodMk continuous_id)).measurable
  unfold hfun
  refine Eq.trans (hmp.lintegral_comp hf).symm ?_
  refine lintegral_congr fun p => ?_
  simp only
  rw [blk_conj, hF _ (blk_unitary hU)]

theorem continuous_gueMat {m : ℕ} : Continuous (fun Z : Fin m → Fin m → ℂ => gueMat Z) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [gueMat, Matrix.smul_apply, Matrix.add_apply, of_apply, conjTranspose_apply, smul_eq_mul]
  fun_prop

/-- One bordering step of the GUE expectation. -/
theorem step_eq {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal) (hFm : Measurable F) :
    ∫⁻ Z, F (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw (n + 1) (n + 1)) =
      ∫⁻ Z', hfun F (gueMat Z') ∂(SpikedWishart.SoftEdge.sampleLaw n n) := by
  have := isProb_cg
  set G : (Fin n → Fin n → ℂ) × ((Fin n → ℂ) × (ℂ × (Fin n → ℂ))) → ENNReal := fun x =>
    F (blk (gueMat x.1) (fun i => rot (x.2.1 i, x.2.2.2 i)) (Real.sqrt 2 * x.2.2.1.re)) with hG
  have hcq : Continuous (fun q : (Fin n → ℂ) × (ℂ × (Fin n → ℂ)) =>
      ((fun i => rot (q.1 i, q.2.2 i)), Real.sqrt 2 * q.2.1.re)) := by
    unfold rot; fun_prop
  have hc : Continuous (fun x : (Fin n → Fin n → ℂ) × ((Fin n → ℂ) × (ℂ × (Fin n → ℂ))) =>
      (gueMat x.1, ((fun i => rot (x.2.1 i, x.2.2.2 i)), Real.sqrt 2 * x.2.2.1.re))) :=
    (continuous_gueMat.comp continuous_fst).prodMk (hcq.comp continuous_snd)
  have hGm : Measurable G := hFm.comp (continuous_blk.comp hc).measurable
  have h1 : ∫⁻ Z, F (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw (n + 1) (n + 1)) =
      ∫⁻ Z, G ((fun i j : Fin n => Z i.castSucc j.castSucc),
        ((fun i : Fin n => Z i.castSucc (Fin.last n)),
          (Z (Fin.last n) (Fin.last n), fun j : Fin n => Z (Fin.last n) j.castSucc)))
        ∂(SpikedWishart.SoftEdge.sampleLaw (n + 1) (n + 1)) := by
    refine lintegral_congr fun Z => ?_
    rw [gueMat_succ]
  rw [h1, (mp_D n).lintegral_comp hGm, lintegral_prod _ hGm.aemeasurable]
  refine lintegral_congr fun Z' => ?_
  have hf : Measurable (fun p : (Fin n → ℂ) × ℝ => F (blk (gueMat Z') p.1 p.2)) :=
    hFm.comp (continuous_blk.comp (continuous_const.prodMk continuous_id)).measurable
  exact (mp_bc n).lintegral_comp hf

theorem measurableSet_Vpos (n : ℕ) : MeasurableSet (Vpos n) := by
  have : Vpos n = ⋂ i : Fin n, {y : Fin (n + 1) → ℝ | 0 < y (Fin.castSucc i)} := by
    ext y; simp [Vpos]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply _)

theorem prod_dexp {n : ℕ} (y : Fin (n + 1) → ℝ) :
    ∏ i : Fin n, dexp (y i.castSucc) =
      (Vpos n).indicator (fun y => Real.exp (-∑ i : Fin n, y i.castSucc)) y := by
  by_cases hy : y ∈ Vpos n
  · rw [Set.indicator_of_mem hy, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [dexp, Set.indicator_of_mem (show y i.castSucc ∈ Set.Ioi 0 from hy i)]
  · rw [Set.indicator_of_notMem hy]
    simp only [Vpos, Set.mem_setOf_eq, not_forall, not_lt] at hy
    obtain ⟨i, hi⟩ := hy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [dexp, Set.indicator_of_notMem (show y i.castSucc ∉ Set.Ioi 0 from not_lt.mpr hi)]

theorem continuous_arrowC_sqrt {n : ℕ} (mu : Fin n → ℝ) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => arrowC mu (fun i => Real.sqrt (p.1 i)) p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp only [arrowC, Matrix.map_apply, arrowR_ll]; fun_prop
  · simp only [arrowC, Matrix.map_apply, arrowR_lc]; fun_prop
  · simp only [arrowC, Matrix.map_apply, arrowR_cl]; fun_prop
  · simp only [arrowC, Matrix.map_apply, arrowR_cc]; fun_prop

theorem exp_gauss_eq {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (hla : la ∈ Ilace mu) :
    Real.exp (-∑ i, wv mu la i) * gaussianPDFReal 0 1 (cv mu la) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((∑ i, mu i ^ 2) / 2) * Real.exp (-(∑ j, la j ^ 2) / 2) := by
  have hsq := sum_sq_la hla
  have e1 : -∑ i, wv mu la i + -(cv mu la) ^ 2 / 2 = (∑ i, mu i ^ 2) / 2 + -(∑ j, la j ^ 2) / 2 := by
    rw [hsq]; ring
  calc _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-∑ i, wv mu la i + -(cv mu la) ^ 2 / 2) := by
        simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Real.exp_add]; ring
    _ = _ := by rw [e1, Real.exp_add]; ring

/-- The border average at a diagonal matrix, by the Dixon-Anderson change of variables. -/
theorem hfun_diag {n : ℕ} (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal) (hFm : Measurable F)
    (hF : ∀ U ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ A, F (U * A * star U) = F A)
    {mu : Fin n → ℝ} (hmu : StrictAnti mu) :
    hfun F (diagonal fun i => (mu i : ℂ)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((∑ i, mu i ^ 2) / 2) / vdm mu) *
        ∫⁻ la in Ilace mu, ENNReal.ofReal (vdm la) * F (diagonal fun j => (la j : ℂ)) *
          ENNReal.ofReal (Real.exp (-(∑ j, la j ^ 2) / 2)) := by
  have := isProb_cg
  have := isProb_exp1
  set G : (Fin n → ℝ) × ℝ → ENNReal := fun p => F (arrowC mu (fun i => Real.sqrt (p.1 i)) p.2) with hG
  have hGm : Measurable G := hFm.comp (continuous_arrowC_sqrt mu).measurable
  have h1 : hfun F (diagonal fun i => (mu i : ℂ)) =
      ∫⁻ p, G (fun i => Complex.normSq (p.1 i), p.2) ∂(nu n) := by
    unfold hfun
    refine lintegral_congr fun p => ?_
    obtain ⟨U, hU, hsim⟩ := blk_diag_similar mu p.1 p.2
    rw [hsim, hF U hU]
    simp only [hG, Complex.norm_def]
  have hmp : MeasurePreserving (fun p : (Fin n → ℂ) × ℝ => ((fun i => Complex.normSq (p.1 i)), p.2)) (nu n)
      ((Measure.pi fun _ : Fin n => exp1).prod (gaussianReal 0 1)) :=
    (mp_normSqvec n).prod (MeasurePreserving.id _)
  rw [h1, hmp.lintegral_comp hGm, lintegral_exp_gauss G hGm]
  have h2 : (fun y : Fin (n + 1) → ℝ => G (Fin.init y, y (Fin.last n)) *
      ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * gaussianPDFReal 0 1 (y (Fin.last n)))) =
      (Vpos n).indicator (fun y => G (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal (Real.exp (-∑ i : Fin n, y i.castSucc) * gaussianPDFReal 0 1 (y (Fin.last n)))) := by
    funext y
    rw [prod_dexp]
    by_cases hy : y ∈ Vpos n <;> simp [hy]
  rw [h2, lintegral_indicator (measurableSet_Vpos n), lintegral_Vpos_eq hmu,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_Ilace mu) fun la hla => ?_
  obtain ⟨U, hU, hsim⟩ := arrowC_similar hla
  have hinit : Fin.init (Phi mu la) = wv mu la := by
    simp only [Phi]; exact Fin.init_snoc _ _
  have hlast : Phi mu la (Fin.last n) = cv mu la := by
    simp only [Phi]; exact Fin.snoc_last _ _
  have hcs : ∀ i : Fin n, Phi mu la i.castSucc = wv mu la i := by
    intro i; simp only [Phi]; exact Fin.snoc_castSucc _ _ _
  simp only [hG, hinit, hlast, hcs]
  rw [hsim, hF U hU, exp_gauss_eq hla]
  have hv : 0 < vdm mu := vdm_pos hmu.injective
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((∑ i, mu i ^ 2) / 2) := by positivity
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_div_of_pos hv, ENNReal.ofReal_div_of_pos hv]
  simp only [div_eq_mul_inv]
  ring

end Weyl

end

-- ===== from W6b.lean =====
section

namespace Weyl

attribute [local instance] matMS matBorel

/-- Unitary invariance of a function of a matrix. -/
def UInv (m : ℕ) (F : Matrix (Fin m) (Fin m) ℂ → ENNReal) : Prop :=
  ∀ U ∈ unitaryGroup (Fin m) ℂ, ∀ A, F (U * A * star U) = F A

theorem continuous_diagR {m : ℕ} :
    Continuous (fun mu : Fin m → ℝ => (diagonal fun i => (mu i : ℂ) : Matrix (Fin m) (Fin m) ℂ)) :=
  (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).matrix_diagonal

theorem continuous_gueWeight (k : ℕ) : Continuous (gueWeight k) := by
  unfold gueWeight; fun_prop

theorem gueWeight_eq {k : ℕ} (ξ : Fin k → ℝ) :
    gueWeight k ξ = vdm ξ ^ 2 * Real.exp (-(∑ i, ξ i ^ 2) / 2) := by
  unfold gueWeight vdm
  rw [← Finset.prod_pow, ← Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => Finset.prod_pow _ _ _
  · congr 1
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem vdm_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (ξ : Fin m → ℝ) : vdm (ξ ∘ σ) = vdm ξ := by
  rw [vdm_eq_abs_det, vdm_eq_abs_det]
  have : vandermonde (ξ ∘ σ) = (vandermonde ξ).submatrix σ id := by
    ext i j; simp [vandermonde_apply]
  rw [this, det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem gueWeight_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (ξ : Fin k → ℝ) :
    gueWeight k (ξ ∘ σ) = gueWeight k ξ := by
  rw [gueWeight_eq, gueWeight_eq, vdm_perm,
    show ∑ i, (ξ ∘ σ) i ^ 2 = ∑ i, ξ i ^ 2 from Equiv.sum_comp σ (fun i => ξ i ^ 2)]

theorem diag_perm_inv {m : ℕ} (F : Matrix (Fin m) (Fin m) ℂ → ENNReal) (hF : UInv m F)
    (σ : Equiv.Perm (Fin m)) (ξ : Fin m → ℝ) :
    F (diagonal fun i => ((ξ ∘ σ) i : ℂ)) = F (diagonal fun i => (ξ i : ℂ)) := by
  have h := perm_conj_diag σ (fun i => (ξ i : ℂ))
  rw [show (fun i => ((ξ ∘ σ) i : ℂ)) = (fun i => (ξ i : ℂ)) ∘ σ from rfl, h, hF _ (perm_mem_unitary σ)]

theorem measurableSet_E (n : ℕ) :
    MeasurableSet {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} := by
  have : {p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.2 ∈ Ilace p.1} =
      ⋂ i : Fin n, ({p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) | p.1 i < p.2 (Fin.castSucc i)} ∩
        {p | p.2 (Fin.succ i) < p.1 i}) := by
    ext p; simp [Ilace]
  rw [this]
  refine MeasurableSet.iInter fun i => (measurableSet_lt ?_ ?_).inter (measurableSet_lt ?_ ?_)
  all_goals fun_prop

/-- The real-number identity behind `h(diag μ) · w(μ) = c₀ Δ(μ) I(μ)`. -/
theorem const_identity {c0 v s : ℝ} (hv : 0 < v) :
    c0 * Real.exp (s / 2) / v * (v ^ 2 * Real.exp (-s / 2)) = c0 * v := by
  have hee : Real.exp (s / 2) * Real.exp (-s / 2) = 1 := by
    rw [← Real.exp_add, show s / 2 + -s / 2 = 0 by ring, Real.exp_zero]
  have : c0 * Real.exp (s / 2) / v * (v ^ 2 * Real.exp (-s / 2)) =
      c0 * v * (Real.exp (s / 2) * Real.exp (-s / 2)) := by
    field_simp
  rw [this, hee, mul_one]

/-- One induction step of the Weyl integration formula. -/
theorem weyl_step {n : ℕ} (C : ENNReal)
    (hC : ∀ F : Matrix (Fin n) (Fin n) ℂ → ENNReal, Measurable F → UInv n F →
      ∫⁻ Z, F (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw n n) =
        C * ∫⁻ ξ, F (diagonal fun i => (ξ i : ℂ)) * ENNReal.ofReal (gueWeight n ξ))
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → ENNReal) (hFm : Measurable F) (hF : UInv (n + 1) F) :
    ∫⁻ Z, F (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw (n + 1) (n + 1)) =
      C * ((n.factorial : ENNReal) * (ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ *
        (ENNReal.ofReal (1 / (n.factorial : ℝ)) * (((n + 1).factorial : ENNReal)⁻¹ *
          ∫⁻ ξ, F (diagonal fun i => (ξ i : ℂ)) * ENNReal.ofReal (gueWeight (n + 1) ξ))))) := by
  classical
  set c0 : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc0
  have hc0n : 0 ≤ c0 := by positivity
  set Φ : (Fin (n + 1) → ℝ) → ENNReal := fun la => ENNReal.ofReal (vdm la) *
    F (diagonal fun j => (la j : ℂ)) * ENNReal.ofReal (Real.exp (-(∑ j, la j ^ 2) / 2)) with hΦ
  have hΦm : Measurable Φ := by
    refine (continuous_vdm.measurable.ennreal_ofReal.mul (hFm.comp continuous_diagR.measurable)).mul ?_
    exact (Continuous.measurable (by fun_prop)).ennreal_ofReal
  have hhm := measurable_hfun F hFm
  have hI : UInv n (hfun F) := fun U hU K => hfun_inv F hFm hF hU K
  rw [step_eq F hFm, hC (hfun F) hhm hI]
  congr 1
  have hHm : Measurable (fun mu : Fin n → ℝ =>
      hfun F (diagonal fun i => (mu i : ℂ)) * ENNReal.ofReal (gueWeight n mu)) :=
    (hhm.comp continuous_diagR.measurable).mul (continuous_gueWeight n).measurable.ennreal_ofReal
  rw [lintegral_sym _ hHm (fun σ mu => by
    rw [diag_perm_inv (hfun F) hI σ mu, gueWeight_perm])]
  congr 1
  -- I(μ) and the joint integrand
  set T : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ENNReal := fun p =>
    if p.2 ∈ Ilace p.1 then ENNReal.ofReal (vdm p.1) * Φ p.2 else 0 with hT
  have hTm : Measurable T :=
    Measurable.ite (measurableSet_E n)
      ((continuous_vdm.measurable.ennreal_ofReal.comp measurable_fst).mul (hΦm.comp measurable_snd))
      measurable_const
  -- step a: the chamber integrand
  have ha : ∫⁻ mu in SA n, hfun F (diagonal fun i => (mu i : ℂ)) * ENNReal.ofReal (gueWeight n mu) =
      ENNReal.ofReal c0 * ∫⁻ mu, ∫⁻ la, T (mu, la) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (measurableSet_SA n)]
    refine lintegral_congr fun mu => ?_
    by_cases hmu : mu ∈ SA n
    · rw [Set.indicator_of_mem hmu, hfun_diag F hFm hF hmu, gueWeight_eq]
      have hv : 0 < vdm mu := vdm_pos (show StrictAnti mu from hmu).injective
      have hin : ∫⁻ la, T (mu, la) = ENNReal.ofReal (vdm mu) * ∫⁻ la in Ilace mu, Φ la := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (measurableSet_Ilace mu)]
        refine lintegral_congr fun la => ?_
        simp only [hT, Set.indicator_apply]
      rw [hin, hΦ]
      calc ENNReal.ofReal (c0 * Real.exp ((∑ i, mu i ^ 2) / 2) / vdm mu) *
            (∫⁻ la in Ilace mu, ENNReal.ofReal (vdm la) * F (diagonal fun j => (la j : ℂ)) *
              ENNReal.ofReal (Real.exp (-(∑ j, la j ^ 2) / 2))) *
            ENNReal.ofReal (vdm mu ^ 2 * Real.exp (-(∑ i, mu i ^ 2) / 2))
          = ENNReal.ofReal (c0 * Real.exp ((∑ i, mu i ^ 2) / 2) / vdm mu *
              (vdm mu ^ 2 * Real.exp (-(∑ i, mu i ^ 2) / 2))) *
            (∫⁻ la in Ilace mu, ENNReal.ofReal (vdm la) * F (diagonal fun j => (la j : ℂ)) *
              ENNReal.ofReal (Real.exp (-(∑ j, la j ^ 2) / 2))) := by
            rw [ENNReal.ofReal_mul (p := c0 * Real.exp ((∑ i, mu i ^ 2) / 2) / vdm mu) (by positivity)]
            ring
        _ = _ := by
            rw [const_identity hv, ENNReal.ofReal_mul hc0n]; ring
    · rw [Set.indicator_of_notMem hmu]
      have hz : ∀ la, T (mu, la) = 0 := by
        intro la
        simp only [hT]
        rw [if_neg]
        intro hla; exact hmu (ilace_mu_strictAnti hla)
      simp [hz]
  -- step c,d: swap and integrate over the box
  have hd : ∫⁻ la, ∫⁻ mu, T (mu, la) =
      ∫⁻ la in SA (n + 1), Φ la * ENNReal.ofReal (vdm la / (n.factorial : ℝ)) := by
    rw [← lintegral_indicator (measurableSet_SA (n + 1))]
    refine lintegral_congr fun la => ?_
    have hbox : ∫⁻ mu, T (mu, la) = (∫⁻ mu in box la, ENNReal.ofReal (vdm mu)) * Φ la := by
      rw [← lintegral_mul_const _ continuous_vdm.measurable.ennreal_ofReal,
        ← lintegral_indicator (measurableSet_box la)]
      refine lintegral_congr fun mu => ?_
      simp only [hT, Set.indicator_apply, mem_box_iff]
    rw [hbox]
    by_cases hla : la ∈ SA (n + 1)
    · rw [Set.indicator_of_mem hla, lintegral_box_vdm (show StrictAnti la from hla), mul_comm]
    · rw [Set.indicator_of_notMem hla]
      have he : box la = ∅ := by
        ext mu
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hmu
        exact hla (ilace_strictAnti (mem_box_iff.mp hmu))
      simp [he]
  -- step e,f: back to the full space
  have hgm : Measurable (fun la : Fin (n + 1) → ℝ =>
      F (diagonal fun i => (la i : ℂ)) * ENNReal.ofReal (gueWeight (n + 1) la)) :=
    (hFm.comp continuous_diagR.measurable).mul (continuous_gueWeight (n + 1)).measurable.ennreal_ofReal
  have he : ∫⁻ la in SA (n + 1), Φ la * ENNReal.ofReal (vdm la / (n.factorial : ℝ)) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) *
        ∫⁻ la in SA (n + 1), F (diagonal fun i => (la i : ℂ)) * ENNReal.ofReal (gueWeight (n + 1) la) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_SA _) fun la _ => ?_
    rw [hΦ, gueWeight_eq, div_eq_mul_one_div, ENNReal.ofReal_mul (vdm_nonneg la),
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (vdm_nonneg la)]
    ring
  have hf : ∫⁻ la in SA (n + 1), F (diagonal fun i => (la i : ℂ)) * ENNReal.ofReal (gueWeight (n + 1) la) =
      (((n + 1).factorial : ENNReal))⁻¹ *
        ∫⁻ la, F (diagonal fun i => (la i : ℂ)) * ENNReal.ofReal (gueWeight (n + 1) la) := by
    rw [lintegral_sym _ hgm (fun σ la => by
      rw [diag_perm_inv F hF σ la, gueWeight_perm]), ← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos _).ne') (ENNReal.natCast_ne_top _),
      one_mul]
  rw [ha, lintegral_lintegral_swap (f := fun mu la => T (mu, la)) hTm.aemeasurable, hd, he, hf]

/-- Weyl integration formula (lintegral form, unnormalised). -/
theorem weyl_lintegral (m : ℕ) : ∃ C : ENNReal, ∀ F : Matrix (Fin m) (Fin m) ℂ → ENNReal,
    Measurable F → UInv m F →
      ∫⁻ Z, F (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw m m) =
        C * ∫⁻ ξ, F (diagonal fun i => (ξ i : ℂ)) * ENNReal.ofReal (gueWeight m ξ) := by
  induction m with
  | zero =>
    refine ⟨1, fun F _ _ => ?_⟩
    have := isProb_cg
    have : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw 0 0) := by
      unfold SpikedWishart.SoftEdge.sampleLaw; infer_instance
    have h1 : ∀ Z : Fin 0 → Fin 0 → ℂ, F (gueMat Z) = F 0 := fun Z => congrArg F (Subsingleton.elim _ _)
    have h2 : ∀ ξ : Fin 0 → ℝ, F (diagonal fun i => (ξ i : ℂ)) * ENNReal.ofReal (gueWeight 0 ξ) = F 0 := by
      intro ξ
      rw [Subsingleton.elim (diagonal fun i => (ξ i : ℂ)) 0]
      simp [gueWeight]
    simp only [h1, h2, lintegral_const, measure_univ, one_mul, mul_one]
    rw [volume_pi, Measure.pi_of_empty]
    simp
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * ((n.factorial : ENNReal) * (ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ *
      (ENNReal.ofReal (1 / (n.factorial : ℝ)) * ((n + 1).factorial : ENNReal)⁻¹))), fun F hFm hF => ?_⟩
    rw [weyl_step C hC F hFm hF]
    ring

end Weyl

end

-- ===== from W6c.lean =====
section

namespace Weyl

attribute [local instance] matMS matBorel

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

/-- Q4: the Weyl integration formula for the largest eigenvalue of the `k × k` GUE. -/
theorem q4_gueMax : Q4_gueMax := by
  intro k _ x
  obtain ⟨C, hC⟩ := weyl_lintegral k
  set S : Set (Matrix (Fin k) (Fin k) ℂ) :=
    {A | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} with hSdef
  have hS : MeasurableSet S := (isClosed_psdSet x).measurableSet
  have := isProb_cg
  have hprob : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw k k) := by
    unfold SpikedWishart.SoftEdge.sampleLaw; infer_instance
  -- normalisation
  have h1 := hC (fun _ => 1) measurable_const (fun _ _ _ => rfl)
  have hZ : ∫⁻ ξ : Fin k → ℝ, (1 : ENNReal) * ENNReal.ofReal (gueWeight k ξ) = ENNReal.ofReal (Z k) := by
    simp only [one_mul]
    rw [Z, ofReal_integral_eq_lintegral_ofReal (gueWeight_integrable k)
      (Filter.Eventually.of_forall (fun ξ => gueWeight_nonneg k ξ))]
  rw [lintegral_const, measure_univ, one_mul, hZ] at h1
  have hCZ : C = (ENNReal.ofReal (Z k))⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left h1.symm
  -- the event
  have hinvS : UInv k (S.indicator 1) := by
    intro U hU A
    by_cases hA : A ∈ S
    · have hA' : U * A * star U ∈ S := (psd_conj_iff x hU A).mpr hA
      simp [Set.indicator_of_mem hA, Set.indicator_of_mem hA']
    · have hA' : U * A * star U ∉ S := fun h => hA ((psd_conj_iff x hU A).mp h)
      rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA']
  have h2 := hC (S.indicator 1) (measurable_one.indicator hS) hinvS
  have hL : ∫⁻ Z, S.indicator 1 (gueMat Z) ∂(SpikedWishart.SoftEdge.sampleLaw k k) =
      SpikedWishart.SoftEdge.sampleLaw k k {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} := by
    exact lintegral_indicator_one (hS.preimage continuous_gueMat.measurable)
  have hR : ∫⁻ ξ, S.indicator 1 (diagonal fun i => (ξ i : ℂ)) * ENNReal.ofReal (gueWeight k ξ) =
      ENNReal.ofReal (∫ ξ in Set.pi Set.univ (fun _ : Fin k => Set.Iic x), gueWeight k ξ) := by
    have hP : MeasurableSet (Set.pi Set.univ (fun _ : Fin k => Set.Iic x)) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Iic)
    rw [ofReal_integral_eq_lintegral_ofReal (gueWeight_integrable k).integrableOn
      (Filter.Eventually.of_forall (fun ξ => gueWeight_nonneg k ξ)), ← lintegral_indicator hP]
    refine lintegral_congr fun ξ => ?_
    by_cases hξ : ξ ∈ Set.pi Set.univ (fun _ : Fin k => Set.Iic x)
    · have hm : (diagonal fun i => (ξ i : ℂ)) ∈ S := (diag_psd_iff x ξ).mpr hξ
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hξ]; simp
    · have hm : (diagonal fun i => (ξ i : ℂ)) ∉ S := fun h => hξ ((diag_psd_iff x ξ).mp h)
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hξ]; simp
  rw [hL, hR, hCZ] at h2
  rw [Measure.real, h2, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Z_pos k).le,
    ENNReal.toReal_ofReal (setIntegral_nonneg
      (MeasurableSet.univ_pi (fun _ => measurableSet_Iic)) (fun ξ _ => gueWeight_nonneg k ξ)), G,
    one_div]

end Weyl

end

end SpikedWishart.Separated.Lib

open SpikedWishart.Separated in
theorem solution :
  ∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ,
    (SpikedWishart.SoftEdge.sampleLaw k k).real
      {Z | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) -
        (Real.sqrt 2 : ℂ)⁻¹ • (Matrix.of Z + (Matrix.of Z)ᴴ)).PosSemidef} = G k x := by
  exact SpikedWishart.Separated.Lib.Weyl.q4_gueMax
