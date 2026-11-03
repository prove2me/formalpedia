-- Prove2me | solution 1 for PowerTwoChoices.Limit.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:33.220505+00:00
-- url     : https://prove2.me/submissions/5e60387b-67a2-4044-8b94-994327159e92

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology
open PowerTwoChoices.Limit

private lemma isState_le_one {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) : x i ≤ 1 := by
  have := hx.2.2 (Nat.zero_le i)
  linarith [hx.1]

private lemma isState_eq_zero_of_ge {x : ℕ → ℝ} (hx : IsState x) {j i : ℕ}
    (hj : x j = 0) (hji : j ≤ i) : x i = 0 := by
  have h1 := hx.2.1 i
  have h2 := hx.2.2 hji
  linarith

private lemma deriv_nonneg_of_max_on_Icc {g : ℝ → ℝ} {t0 d : ℝ}
    (ht0 : 0 < t0) (hd : HasDerivWithinAt g d (Set.Ici 0) t0)
    (hmax : ∀ t ∈ Set.Icc 0 t0, g t ≤ g t0) : 0 ≤ d := by
  have hd_at : HasDerivAt g d t0 := hd.hasDerivAt (Ici_mem_nhds ht0)
  have hd_lt : HasDerivWithinAt g d (Set.Iio t0) t0 := hd_at.hasDerivWithinAt
  have hdiff : Set.Iio t0 \ {t0} = Set.Iio t0 :=
    Set.diff_singleton_eq_self (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff] at hd_lt
  have hmem : Set.Ico 0 t0 ∈ 𝓝[<] t0 := Ico_mem_nhdsLT ht0
  have h_nonneg : ∀ᶠ t in 𝓝[<] t0, 0 ≤ slope g t0 t := by
    filter_upwards [hmem] with t ht
    rw [slope_def_field]
    have hle : g t - g t0 ≤ 0 := sub_nonpos.mpr (hmax t ⟨ht.1, ht.2.le⟩)
    have hlt : t - t0 < 0 := sub_neg.mpr ht.2
    exact div_nonneg_of_nonpos hle hlt.le
  exact ge_of_tendsto hd_lt h_nonneg

private lemma nonpos_of_hasDerivWithinAt_neg {g g' : ℝ → ℝ}
    (hg0 : g 0 ≤ 0)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g (g' t) (Set.Ici 0) t)
    (hneg : ∀ t : ℝ, 0 < t → 0 < g t → g' t < 0)
    {T : ℝ} (hT : 0 ≤ T) : g T ≤ 0 := by
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    intro t ht
    exact ((hderiv t ht.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hcont with ⟨t0, ht0, hmax⟩
  have hT_le : g T ≤ g t0 := hmax (Set.right_mem_Icc.mpr hT)
  by_contra hpos
  push_neg at hpos
  have ht0_pos : 0 < g t0 := lt_of_lt_of_le hpos hT_le
  have ht0_ne : t0 ≠ 0 := by
    intro h0
    subst h0
    linarith
  have ht0_gt : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
  have hd_nonneg : 0 ≤ g' t0 :=
    deriv_nonneg_of_max_on_Icc ht0_gt (hderiv t0 ht0.1)
      (fun t ht => hmax ⟨ht.1, ht.2.trans ht0.2⟩)
  have hd_neg : g' t0 < 0 := hneg t0 ht0_gt ht0_pos
  linarith

private lemma sum_range_geom_succ (d k : ℕ) :
    ∑ r ∈ Finset.range (k + 1), d ^ r = 1 + (∑ r ∈ Finset.range k, d ^ r) * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [pow_succ]
    ring

private lemma fixedPoint_succ (lam : ℝ) (d k : ℕ) :
    fixedPoint lam d (k + 1) = lam * (fixedPoint lam d k) ^ d := by
  unfold fixedPoint
  rw [sum_range_geom_succ, pow_add, pow_one, pow_mul]

private lemma fixedPoint_zero (lam : ℝ) (d : ℕ) : fixedPoint lam d 0 = 1 := by
  simp [fixedPoint]

private lemma fixedPoint_nonneg {lam : ℝ} (hlam0 : 0 < lam) (d i : ℕ) :
    0 ≤ fixedPoint lam d i :=
  pow_nonneg hlam0.le _

private lemma fixedPoint_le_one {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (d i : ℕ) :
    fixedPoint lam d i ≤ 1 :=
  pow_le_one₀ hlam0.le hlam1.le

private lemma fixedPoint_drift_eq_zero (lam : ℝ) (d i : ℕ) (hi : 1 ≤ i) :
    drift lam d (fixedPoint lam d) i = 0 := by
  unfold drift
  have h1 : fixedPoint lam d i = lam * (fixedPoint lam d (i - 1)) ^ d := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, fixedPoint_succ]
  have h2 := fixedPoint_succ lam d i
  linarith

private lemma fixedPoint_le_pow_self {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (i : ℕ) :
    fixedPoint lam d i ≤ lam ^ i := by
  unfold fixedPoint
  apply pow_le_pow_of_le_one hlam0.le hlam1.le
  have : ∑ k ∈ Finset.range i, 1 ≤ ∑ k ∈ Finset.range i, d ^ k := by
    apply Finset.sum_le_sum
    intro k _
    exact Nat.one_le_pow k d (by omega)
  simpa using this

private lemma abs_pow_sub_pow_le_aux {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ m : ℕ, |x ^ (m + 1) - y ^ (m + 1)| ≤ (1 + (m : ℝ) * y) * |x - y|
  | 0 => by simp
  | m + 1 => by
    have hsplit : x ^ (m + 2) - y ^ (m + 2) =
        x * (x ^ (m + 1) - y ^ (m + 1)) + y ^ (m + 1) * (x - y) := by ring
    rw [hsplit]
    have htri := abs_add_le (x * (x ^ (m + 1) - y ^ (m + 1))) (y ^ (m + 1) * (x - y))
    rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg (pow_nonneg hy0 _)] at htri
    have ih := abs_pow_sub_pow_le_aux hx0 hx1 hy0 hy1 m
    have h1 : x * |x ^ (m + 1) - y ^ (m + 1)| ≤ 1 * ((1 + (m : ℝ) * y) * |x - y|) := by
      calc x * |x ^ (m + 1) - y ^ (m + 1)| ≤ 1 * |x ^ (m + 1) - y ^ (m + 1)| :=
            mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
        _ ≤ 1 * ((1 + (m : ℝ) * y) * |x - y|) :=
            mul_le_mul_of_nonneg_left ih zero_le_one
    have hy_pow : y ^ (m + 1) ≤ y ^ 1 :=
      pow_le_pow_of_le_one hy0 hy1 (Nat.le_add_left 1 m)
    rw [pow_one] at hy_pow
    have h2 : y ^ (m + 1) * |x - y| ≤ y * |x - y| :=
      mul_le_mul_of_nonneg_right hy_pow (abs_nonneg _)
    push_cast
    linarith

private lemma mul_pow_sub_pow_eq_abs {x y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (d : ℕ) :
    (x - y) * (x ^ d - y ^ d) = |x - y| * |x ^ d - y ^ d| := by
  rcases le_total y x with h | h
  · have hd : y ^ d ≤ x ^ d := pow_le_pow_left₀ hy0 h d
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr hd)]
  · have hd : x ^ d ≤ y ^ d := pow_le_pow_left₀ hx0 h d
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr hd)]
    ring

private noncomputable def cSeq (lam : ℝ) (d i : ℕ) : ℝ :=
  lam * (1 + ((d - 1 : ℕ) : ℝ) * fixedPoint lam d i)

private lemma cSeq_ge_lam {lam : ℝ} (hlam0 : 0 < lam) (d i : ℕ) :
    lam ≤ cSeq lam d i := by
  unfold cSeq
  have : 0 ≤ ((d - 1 : ℕ) : ℝ) * fixedPoint lam d i :=
    mul_nonneg (Nat.cast_nonneg _) (fixedPoint_nonneg hlam0 d i)
  nlinarith

private lemma cSeq_pos {lam : ℝ} (hlam0 : 0 < lam) (d i : ℕ) :
    0 < cSeq lam d i :=
  lt_of_lt_of_le hlam0 (cSeq_ge_lam hlam0 d i)

private lemma abs_lam_pow_sub_le_cSeq {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    |lam * (x ^ d - fixedPoint lam d i ^ d)| ≤ cSeq lam d i * |x - fixedPoint lam d i| := by
  rw [abs_mul, abs_of_pos hlam0]
  unfold cSeq
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hlam0.le
  have h1 := abs_pow_sub_pow_le_aux hx0 hx1 (fixedPoint_nonneg hlam0 d i)
    (fixedPoint_le_one hlam0 hlam1 d i) (d - 1)
  have hd_eq : (d - 1) + 1 = d := by omega
  rwa [hd_eq] at h1

private noncomputable def deltaSeq (lam : ℝ) (d I : ℕ) (η0 R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    if k + 1 < I then ((1 - η0) / cSeq lam d (k + 1)) * deltaSeq lam d I η0 R k
    else R * deltaSeq lam d I η0 R k

private lemma deltaSeq_zero (lam : ℝ) (d I : ℕ) (η0 R : ℝ) :
    deltaSeq lam d I η0 R 0 = 1 := rfl

private lemma deltaSeq_succ_lt (lam : ℝ) (d I : ℕ) (η0 R : ℝ) (k : ℕ) (h : k + 1 < I) :
    deltaSeq lam d I η0 R (k + 1) = ((1 - η0) / cSeq lam d (k + 1)) * deltaSeq lam d I η0 R k := by
  rw [deltaSeq, if_pos h]

private lemma deltaSeq_succ_ge (lam : ℝ) (d I : ℕ) (η0 R : ℝ) (k : ℕ) (h : I ≤ k + 1) :
    deltaSeq lam d I η0 R (k + 1) = R * deltaSeq lam d I η0 R k := by
  rw [deltaSeq, if_neg (by omega)]

private noncomputable def wSeq (lam : ℝ) (d I : ℕ) (η0 R : ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, deltaSeq lam d I η0 R k

private lemma deltaSeq_pos {lam : ℝ} {d I : ℕ} {η0 R : ℝ}
    (hlam0 : 0 < lam) (hη0 : η0 < 1) (hR : 0 < R) :
    ∀ k : ℕ, 0 < deltaSeq lam d I η0 R k
  | 0 => zero_lt_one
  | k + 1 => by
    unfold deltaSeq
    split_ifs
    · have hc := cSeq_pos hlam0 d (k + 1)
      have hnum : 0 < 1 - η0 := by linarith
      exact mul_pos (div_pos hnum hc) (deltaSeq_pos hlam0 hη0 hR k)
    · exact mul_pos hR (deltaSeq_pos hlam0 hη0 hR k)

private lemma wSeq_zero (lam : ℝ) (d I : ℕ) (η0 R : ℝ) :
    wSeq lam d I η0 R 0 = 0 := by
  simp [wSeq]

private lemma wSeq_one (lam : ℝ) (d I : ℕ) (η0 R : ℝ) :
    wSeq lam d I η0 R 1 = 1 := by
  simp [wSeq, deltaSeq]

private lemma wSeq_succ (lam : ℝ) (d I : ℕ) (η0 R : ℝ) (k : ℕ) :
    wSeq lam d I η0 R (k + 1) = wSeq lam d I η0 R k + deltaSeq lam d I η0 R k := by
  simp [wSeq, Finset.sum_range_succ]

private lemma wSeq_ge_one {lam : ℝ} {d I : ℕ} {η0 R : ℝ}
    (hlam0 : 0 < lam) (hη0 : η0 < 1) (hR : 0 < R) :
    ∀ i : ℕ, 1 ≤ i → 1 ≤ wSeq lam d I η0 R i := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  induction k with
  | zero => rw [wSeq_one]
  | succ k ih =>
    rw [wSeq_succ]
    have hpos := deltaSeq_pos (I := I) (d := d) hlam0 hη0 hR (k + 1)
    have hih := ih (by omega)
    linarith

private lemma wSeq_nonneg {lam : ℝ} {d I : ℕ} {η0 R : ℝ}
    (hlam0 : 0 < lam) (hη0 : η0 < 1) (hR : 0 < R) (i : ℕ) :
    0 ≤ wSeq lam d I η0 R i := by
  by_cases hi : i = 0
  · subst hi; simp [wSeq_zero]
  · have := wSeq_ge_one (I := I) (d := d) hlam0 hη0 hR i (by omega)
    linarith

private lemma wSeq_mono {lam : ℝ} {d I : ℕ} {η0 R : ℝ}
    (hlam0 : 0 < lam) (hη0 : η0 < 1) (hR : 0 < R) :
    Monotone (wSeq lam d I η0 R) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [wSeq_succ]
  have := deltaSeq_pos (I := I) (d := d) hlam0 hη0 hR k
  linarith

private lemma exists_weights (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ (w : ℕ → ℝ) (δ A S_pi : ℝ),
      w 0 = 0 ∧
      w 1 = 1 ∧
      (∀ i : ℕ, 1 ≤ i → 1 ≤ w i) ∧
      (∀ i : ℕ, 0 ≤ w i) ∧
      Monotone w ∧
      0 < δ ∧
      2 ≤ A ∧
      0 < S_pi ∧
      (∀ i : ℕ, 1 ≤ i → w (i + 1) ≤ A * w i) ∧
      (∀ k : ℕ, cSeq lam d (k + 1) * (w (k + 2) - w (k + 1)) - (w (k + 1) - w k) ≤
        -δ * w (k + 1)) ∧
      (∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1) ≤ S_pi) ∧
      (∀ B : ℝ, ∃ N_B : ℕ, ∀ i : ℕ, N_B ≤ i → B < w i) := by
  let q : ℝ := (1 + lam) / 2
  have hq_gt_lam : lam < q := by dsimp [q]; linarith
  have hq_lt_one : q < 1 := by dsimp [q]; linarith
  have hq_pos : 0 < q := lt_trans hlam0 hq_gt_lam
  let R : ℝ := (1 + q) / (2 * q)
  have hR_gt_one : 1 < R := by
    dsimp [R]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hR_pos : 0 < R := lt_trans zero_lt_one hR_gt_one
  let η0 : ℝ := (1 - q) / 2
  have hη0_pos : 0 < η0 := by dsimp [η0]; linarith
  have hη0_lt_one : η0 < 1 := by dsimp [η0]; linarith
  have hqR_eq : q * R = 1 - η0 := by
    dsimp [R, η0]
    field_simp [hq_pos.ne']
    ring
  have hRlam_lt_one : R * lam < 1 := by
    have hR_lt : R < 1 / q := by
      dsimp [R]
      rw [div_lt_div_iff₀ (by positivity) hq_pos]
      nlinarith
    calc R * lam < (1 / q) * lam := mul_lt_mul_of_pos_right hR_lt hlam0
      _ = lam / q := one_div_mul_eq_div q lam
      _ < 1 := (div_lt_one hq_pos).mpr hq_gt_lam
  have hd1_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    have : 1 ≤ d - 1 := by omega
    exact_mod_cast this
  obtain ⟨I0, hI0⟩ := exists_pow_lt_of_lt_one
    (div_pos (sub_pos.mpr hq_gt_lam) (mul_pos hlam0 hd1_pos)) hlam1
  let I : ℕ := max I0 1
  have hI_ge_one : 1 ≤ I := le_max_right I0 1
  have hc_le_q : ∀ i : ℕ, I ≤ i → cSeq lam d i ≤ q := by
    intro i hi
    unfold cSeq
    have hi0 : I0 ≤ i := le_trans (le_max_left I0 1) hi
    have hfp : fixedPoint lam d i ≤ (q - lam) / (lam * ((d - 1 : ℕ) : ℝ)) := by
      calc fixedPoint lam d i ≤ lam ^ i := fixedPoint_le_pow_self hd hlam0 hlam1 i
        _ ≤ lam ^ I0 := pow_le_pow_of_le_one hlam0.le hlam1.le hi0
        _ ≤ (q - lam) / (lam * ((d - 1 : ℕ) : ℝ)) := hI0.le
    have hmul : lam * (((d - 1 : ℕ) : ℝ) * fixedPoint lam d i) ≤ q - lam := by
      have hpos : 0 < lam * ((d - 1 : ℕ) : ℝ) := mul_pos hlam0 hd1_pos
      have := (le_div_iff₀ hpos).mp hfp
      linarith
    linarith
  let Δ : ℕ → ℝ := deltaSeq lam d I η0 R
  let w : ℕ → ℝ := wSeq lam d I η0 R
  have hΔ_pos : ∀ k : ℕ, 0 < Δ k := deltaSeq_pos hlam0 hη0_lt_one hR_pos
  have hcΔ_le : ∀ k : ℕ, cSeq lam d (k + 1) * Δ (k + 1) ≤ (1 - η0) * Δ k := by
    intro k
    by_cases hlt : k + 1 < I
    · have hΔ_eq : Δ (k + 1) = ((1 - η0) / cSeq lam d (k + 1)) * Δ k :=
        deltaSeq_succ_lt lam d I η0 R k hlt
      have hc_ne : cSeq lam d (k + 1) ≠ 0 := (cSeq_pos hlam0 d (k + 1)).ne'
      rw [hΔ_eq]
      calc cSeq lam d (k + 1) * (((1 - η0) / cSeq lam d (k + 1)) * Δ k)
          = (cSeq lam d (k + 1) * ((1 - η0) / cSeq lam d (k + 1))) * Δ k := by ring
        _ ≤ (1 - η0) * Δ k := le_of_eq (by rw [mul_div_cancel₀ _ hc_ne])
    · push_neg at hlt
      have hΔ_eq : Δ (k + 1) = R * Δ k :=
        deltaSeq_succ_ge lam d I η0 R k hlt
      have hcq : cSeq lam d (k + 1) ≤ q := hc_le_q (k + 1) hlt
      rw [hΔ_eq]
      calc cSeq lam d (k + 1) * (R * Δ k)
          = (cSeq lam d (k + 1) * R) * Δ k := by ring
        _ ≤ (q * R) * Δ k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcq hR_pos.le) (hΔ_pos k).le
        _ = (1 - η0) * Δ k := by rw [hqR_eq]
  let M0 : ℝ := 1 + ∑ j ∈ Finset.range I, (w (j + 1) / Δ j)
  have hM0_pos : 0 < M0 := by
    have : 0 ≤ ∑ j ∈ Finset.range I, (w (j + 1) / Δ j) := by
      apply Finset.sum_nonneg
      intro j _
      exact div_nonneg (wSeq_nonneg hlam0 hη0_lt_one hR_pos (j + 1)) (hΔ_pos j).le
    dsimp [M0]; linarith
  let Mw : ℝ := max M0 (R / (R - 1))
  have hMw_pos : 0 < Mw := lt_of_lt_of_le hM0_pos (le_max_left _ _)
  have hw_le_Mw_Δ : ∀ k : ℕ, w (k + 1) ≤ Mw * Δ k := by
    intro k
    induction k with
    | zero =>
      have h0 : 0 ∈ Finset.range I := Finset.mem_range.mpr hI_ge_one
      have hle : w 1 / Δ 0 ≤ ∑ j ∈ Finset.range I, (w (j + 1) / Δ j) :=
        Finset.single_le_sum (fun j _ => div_nonneg (wSeq_nonneg hlam0 hη0_lt_one hR_pos (j + 1)) (hΔ_pos j).le) h0
      have hM0 : w 1 / Δ 0 ≤ Mw := by
        calc w 1 / Δ 0 ≤ M0 := by dsimp [M0]; linarith
          _ ≤ Mw := le_max_left _ _
      exact (div_le_iff₀ (hΔ_pos 0)).mp hM0
    | succ k ih =>
      by_cases hlt : k + 1 < I
      · have hk_mem : k + 1 ∈ Finset.range I := Finset.mem_range.mpr hlt
        have hle : w (k + 2) / Δ (k + 1) ≤ ∑ j ∈ Finset.range I, (w (j + 1) / Δ j) :=
          Finset.single_le_sum (fun j _ => div_nonneg (wSeq_nonneg hlam0 hη0_lt_one hR_pos (j + 1)) (hΔ_pos j).le) hk_mem
        have hM0 : w (k + 2) / Δ (k + 1) ≤ Mw := by
          calc w (k + 2) / Δ (k + 1) ≤ M0 := by dsimp [M0]; linarith
            _ ≤ Mw := le_max_left _ _
        exact (div_le_iff₀ (hΔ_pos (k + 1))).mp hM0
      · push_neg at hlt
        have hΔ_eq : Δ (k + 1) = R * Δ k := deltaSeq_succ_ge lam d I η0 R k hlt
        have hMw_R : Mw + R ≤ Mw * R := by
          have h1 : R / (R - 1) ≤ Mw := le_max_right _ _
          have h2 : R ≤ Mw * (R - 1) := (div_le_iff₀ (by linarith)).mp h1
          linarith
        have hw_succ : w (k + 2) = w (k + 1) + Δ (k + 1) := wSeq_succ lam d I η0 R (k + 1)
        rw [hw_succ, hΔ_eq]
        calc w (k + 1) + R * Δ k ≤ Mw * Δ k + R * Δ k := by linarith
          _ = (Mw + R) * Δ k := by ring
          _ ≤ (Mw * R) * Δ k := mul_le_mul_of_nonneg_right hMw_R (hΔ_pos k).le
          _ = Mw * (R * Δ k) := by ring
  let δ : ℝ := η0 / Mw
  have hδ_pos : 0 < δ := div_pos hη0_pos hMw_pos
  have h_recur : ∀ k : ℕ, cSeq lam d (k + 1) * (w (k + 2) - w (k + 1)) - (w (k + 1) - w k) ≤
      -δ * w (k + 1) := by
    intro k
    have hd1 : w (k + 2) - w (k + 1) = Δ (k + 1) := by
      have := wSeq_succ lam d I η0 R (k + 1); linarith
    have hd0 : w (k + 1) - w k = Δ k := by
      have := wSeq_succ lam d I η0 R k; linarith
    rw [hd1, hd0]
    have h1 := hcΔ_le k
    have h2 : δ * w (k + 1) ≤ η0 * Δ k := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hMw_pos]
      linarith [mul_le_mul_of_nonneg_left (hw_le_Mw_Δ k) hη0_pos.le]
    linarith
  let A : ℝ := 2 + R + 1 / lam
  have h1_div_lam_pos : 0 < 1 / lam := div_pos zero_lt_one hlam0
  have hA_ge_two : 2 ≤ A := by dsimp [A]; linarith
  have hΔ_step_le : ∀ k : ℕ, Δ k ≤ (A - 1) * w k + (if k = 0 then 1 else 0) := by
    intro k
    cases k with
    | zero =>
      have hw0_eq : w 0 = 0 := wSeq_zero lam d I η0 R
      have hΔ0_eq : Δ 0 = 1 := deltaSeq_zero lam d I η0 R
      rw [hw0_eq, hΔ0_eq]
      simp
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k), add_zero]
      have hwk : Δ k ≤ w (k + 1) := by
        have hws := wSeq_succ lam d I η0 R k
        have hwn := wSeq_nonneg (I := I) (d := d) hlam0 hη0_lt_one hR_pos k
        change w (k + 1) = w k + Δ k at hws
        change 0 ≤ w k at hwn
        linarith
      by_cases hlt : k + 1 < I
      · have hΔ_eq : Δ (k + 1) = ((1 - η0) / cSeq lam d (k + 1)) * Δ k :=
          deltaSeq_succ_lt lam d I η0 R k hlt
        rw [hΔ_eq]
        have hc : lam ≤ cSeq lam d (k + 1) := cSeq_ge_lam hlam0 d (k + 1)
        have hdiv : (1 - η0) / cSeq lam d (k + 1) ≤ 1 / lam := by
          calc (1 - η0) / cSeq lam d (k + 1) ≤ 1 / cSeq lam d (k + 1) :=
                div_le_div_of_nonneg_right (by linarith) (cSeq_pos hlam0 d (k + 1)).le
            _ ≤ 1 / lam := one_div_le_one_div_of_le hlam0 hc
        have h1 : (1 / lam) ≤ A - 1 := by dsimp [A]; linarith
        calc ((1 - η0) / cSeq lam d (k + 1)) * Δ k ≤ (1 / lam) * Δ k :=
              mul_le_mul_of_nonneg_right hdiv (hΔ_pos k).le
          _ ≤ (A - 1) * Δ k := mul_le_mul_of_nonneg_right h1 (hΔ_pos k).le
          _ ≤ (A - 1) * w (k + 1) := mul_le_mul_of_nonneg_left hwk (by linarith)
      · push_neg at hlt
        have hΔ_eq : Δ (k + 1) = R * Δ k := deltaSeq_succ_ge lam d I η0 R k hlt
        rw [hΔ_eq]
        have h1 : R ≤ A - 1 := by dsimp [A]; linarith
        calc R * Δ k ≤ (A - 1) * Δ k := mul_le_mul_of_nonneg_right h1 (hΔ_pos k).le
          _ ≤ (A - 1) * w (k + 1) := mul_le_mul_of_nonneg_left hwk (by linarith)
  have hw_step_A : ∀ i : ℕ, 1 ≤ i → w (i + 1) ≤ A * w i := by
    intro i hi
    have h1 := hΔ_step_le i
    rw [if_neg (by omega), add_zero] at h1
    have h2 := wSeq_succ lam d I η0 R i
    linarith
  let CΔ : ℝ := 1 + ∑ j ∈ Finset.range I, Δ j
  have hCΔ_pos : 0 < CΔ := by
    have : 0 ≤ ∑ j ∈ Finset.range I, Δ j :=
      Finset.sum_nonneg (fun j _ => (hΔ_pos j).le)
    dsimp [CΔ]; linarith
  have hΔ_geom : ∀ k : ℕ, Δ k ≤ CΔ * R ^ k := by
    intro k
    induction k with
    | zero =>
      have : (1 : ℝ) ≤ CΔ := by
        have : 0 ≤ ∑ j ∈ Finset.range I, Δ j :=
          Finset.sum_nonneg (fun j _ => (hΔ_pos j).le)
        dsimp [CΔ]; linarith
      simpa [Δ, deltaSeq] using this
    | succ k ih =>
      by_cases hlt : k + 1 < I
      · have hk_mem : k + 1 ∈ Finset.range I := Finset.mem_range.mpr hlt
        have hle : Δ (k + 1) ≤ ∑ j ∈ Finset.range I, Δ j :=
          Finset.single_le_sum (fun j _ => (hΔ_pos j).le) hk_mem
        have h1 : Δ (k + 1) ≤ CΔ := by dsimp [CΔ]; linarith
        have hR_pow : (1 : ℝ) ≤ R ^ (k + 1) := one_le_pow₀ hR_gt_one.le
        calc Δ (k + 1) ≤ CΔ * 1 := by linarith
          _ ≤ CΔ * R ^ (k + 1) := mul_le_mul_of_nonneg_left hR_pow hCΔ_pos.le
      · push_neg at hlt
        have hΔ_eq : Δ (k + 1) = R * Δ k := deltaSeq_succ_ge lam d I η0 R k hlt
        rw [hΔ_eq, pow_succ']
        calc R * Δ k ≤ R * (CΔ * R ^ k) := mul_le_mul_of_nonneg_left ih hR_pos.le
          _ = CΔ * (R * R ^ k) := by ring
  let S_pi : ℝ := (Mw * CΔ * lam) / (1 - R * lam)
  have hSpi_pos : 0 < S_pi := by
    dsimp [S_pi]
    exact div_pos (by positivity) (by linarith)
  have hsum_pi : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1) ≤ S_pi := by
    intro K
    have hterm : ∀ k : ℕ, w (k + 1) * fixedPoint lam d (k + 1) ≤
        (Mw * CΔ * lam) * (R * lam) ^ k := by
      intro k
      have hw_bound : w (k + 1) ≤ Mw * (CΔ * R ^ k) :=
        le_trans (hw_le_Mw_Δ k) (mul_le_mul_of_nonneg_left (hΔ_geom k) hMw_pos.le)
      have hfp_bound : fixedPoint lam d (k + 1) ≤ lam ^ (k + 1) :=
        fixedPoint_le_pow_self hd hlam0 hlam1 (k + 1)
      calc w (k + 1) * fixedPoint lam d (k + 1)
          ≤ (Mw * (CΔ * R ^ k)) * lam ^ (k + 1) :=
            mul_le_mul hw_bound hfp_bound (fixedPoint_nonneg hlam0 d (k + 1)) (by positivity)
        _ = (Mw * CΔ * lam) * (R ^ k * lam ^ k) := by rw [pow_succ']; ring
        _ = (Mw * CΔ * lam) * (R * lam) ^ k := by rw [mul_pow]
    have hgeom_sum : ∑ k ∈ Finset.range K, (R * lam) ^ k ≤ 1 / (1 - R * lam) := by
      have h1 : (1 - R * lam) * ∑ k ∈ Finset.range K, (R * lam) ^ k = 1 - (R * lam) ^ K := by
        have := geom_sum_mul_neg (R * lam) K
        linarith
      have h2 : 0 ≤ (R * lam) ^ K := by positivity
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc ∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1)
        ≤ ∑ k ∈ Finset.range K, (Mw * CΔ * lam) * (R * lam) ^ k :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (Mw * CΔ * lam) * ∑ k ∈ Finset.range K, (R * lam) ^ k := by rw [← Finset.mul_sum]
      _ ≤ (Mw * CΔ * lam) * (1 / (1 - R * lam)) :=
          mul_le_mul_of_nonneg_left hgeom_sum (by positivity)
      _ = S_pi := by dsimp [S_pi]; ring
  have hw_unbounded : ∀ B : ℝ, ∃ N_B : ℕ, ∀ i : ℕ, N_B ≤ i → B < w i := by
    intro B
    have hΔ_ge : ∀ m : ℕ, Δ (I - 1) * R ^ m ≤ Δ (I - 1 + m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hstep : Δ (I - 1 + (m + 1)) = R * Δ (I - 1 + m) := by
          have hrew : I - 1 + (m + 1) = (I - 1 + m) + 1 := by omega
          rw [hrew]
          exact deltaSeq_succ_ge lam d I η0 R (I - 1 + m) (by omega)
        rw [hstep, pow_succ']
        calc Δ (I - 1) * (R * R ^ m) = R * (Δ (I - 1) * R ^ m) := by ring
          _ ≤ R * Δ (I - 1 + m) := mul_le_mul_of_nonneg_left ih hR_pos.le
    obtain ⟨m0, hm0⟩ := exists_nat_gt (max B 0 / (Δ (I - 1) * (R - 1)))
    refine ⟨I + m0, ?_⟩
    intro i hi
    have h_rpow : 1 + (m0 : ℝ) * (R - 1) ≤ R ^ m0 := by
      simpa using one_add_mul_sub_le_pow (by linarith : -1 ≤ R) m0
    have hB_lt : B < Δ (I - 1) * R ^ m0 := by
      have hpos : 0 < Δ (I - 1) * (R - 1) := mul_pos (hΔ_pos (I - 1)) (by linarith)
      have h1 : max B 0 < (m0 : ℝ) * (Δ (I - 1) * (R - 1)) := (div_lt_iff₀ hpos).mp hm0
      have h2 : B ≤ max B 0 := le_max_left B 0
      nlinarith [hΔ_pos (I - 1)]
    have hw_ge_Δ : Δ (I - 1 + m0) ≤ w (I + m0) := by
      have hrew : I + m0 = (I - 1 + m0) + 1 := by omega
      have hws := wSeq_succ lam d I η0 R (I - 1 + m0)
      have hwn := wSeq_nonneg (I := I) (d := d) hlam0 hη0_lt_one hR_pos (I - 1 + m0)
      change w (I - 1 + m0 + 1) = w (I - 1 + m0) + Δ (I - 1 + m0) at hws
      change 0 ≤ w (I - 1 + m0) at hwn
      rw [hrew]
      linarith
    have hw_mono : w (I + m0) ≤ w i :=
      wSeq_mono hlam0 hη0_lt_one hR_pos hi
    linarith [hΔ_ge m0]
  exact ⟨w, δ, A, S_pi, wSeq_zero lam d I η0 R, wSeq_one lam d I η0 R,
    wSeq_ge_one hlam0 hη0_lt_one hR_pos, wSeq_nonneg hlam0 hη0_lt_one hR_pos,
    wSeq_mono hlam0 hη0_lt_one hR_pos, hδ_pos, hA_ge_two, hSpi_pos,
    hw_step_A, h_recur, hsum_pi, hw_unbounded⟩

private lemma drift_le_prev_pow {lam : ℝ} {d : ℕ} (hlam0 : 0 < lam)
    {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) :
    drift lam d x i ≤ lam * x (i - 1) ^ d := by
  unfold drift
  have h1 : 0 ≤ lam * x i ^ d := mul_nonneg hlam0.le (pow_nonneg (hx.2.1 i) d)
  have h2 : x (i + 1) ≤ x i := hx.2.2 (Nat.le_succ i)
  linarith

private lemma drift_le_prev {lam : ℝ} {d : ℕ} (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) :
    drift lam d x i ≤ x (i - 1) := by
  have h1 := drift_le_prev_pow (d := d) hlam0 hx i
  have h2 : x (i - 1) ^ d ≤ x (i - 1) ^ 1 :=
    pow_le_pow_of_le_one (hx.2.1 _) (isState_le_one hx _) (by omega)
  rw [pow_one] at h2
  have h3 : lam * x (i - 1) ^ d ≤ 1 * x (i - 1) :=
    mul_le_mul hlam1.le h2 (pow_nonneg (hx.2.1 _) d) zero_le_one
  linarith

private lemma drift_le_prev_sq {lam : ℝ} {d : ℕ} (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) :
    drift lam d x i ≤ x (i - 1) ^ 2 := by
  have h1 := drift_le_prev_pow (d := d) hlam0 hx i
  have h2 : x (i - 1) ^ d ≤ x (i - 1) ^ 2 :=
    pow_le_pow_of_le_one (hx.2.1 _) (isState_le_one hx _) hd
  have h3 : lam * x (i - 1) ^ d ≤ 1 * x (i - 1) ^ 2 :=
    mul_le_mul hlam1.le h2 (pow_nonneg (hx.2.1 _) d) zero_le_one
  linarith

private lemma sum_weighted_drift_le {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {x : ℕ → ℝ} (hx : IsState x)
    {w : ℕ → ℝ} {A : ℝ} (hw1 : w 1 = 1) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i) :
    ∀ K : ℕ, ∑ k ∈ Finset.range (K + 1), w (k + 1) * drift lam d x (k + 1) ≤
      1 + A * ∑ k ∈ Finset.range K, w (k + 1) * x (k + 1)
  | 0 => by
    rw [Finset.sum_range_one, Finset.sum_range_zero, mul_zero, add_zero, zero_add, hw1, one_mul]
    have h1 := drift_le_prev hd hlam0 hlam1 hx 1
    simpa [hx.1] using h1
  | K + 1 => by
    conv_lhs => rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    have ih := sum_weighted_drift_le hd hlam0 hlam1 hx hw1 hw_nonneg hwA K
    have hdr := drift_le_prev hd hlam0 hlam1 hx (K + 2)
    have hw_step : w (K + 2) ≤ A * w (K + 1) := hwA (K + 1) (by omega)
    have hstep : w (K + 2) * drift lam d x (K + 2) ≤ A * (w (K + 1) * x (K + 1)) := by
      calc w (K + 2) * drift lam d x (K + 2)
          ≤ w (K + 2) * x (K + 1) := mul_le_mul_of_nonneg_left hdr (hw_nonneg _)
        _ ≤ (A * w (K + 1)) * x (K + 1) := mul_le_mul_of_nonneg_right hw_step (hx.2.1 _)
        _ = A * (w (K + 1) * x (K + 1)) := by ring
    linarith

private lemma hasDerivWithinAt_weighted_sum {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}
    (hs : IsTrajectory lam d s) (w : ℕ → ℝ) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => ∑ k ∈ Finset.range K, w (k + 1) * s u (k + 1))
      (∑ k ∈ Finset.range K, w (k + 1) * drift lam d (s t) (k + 1)) (Set.Ici 0) t := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact hasDerivWithinAt_const t (Set.Ici 0) (0 : ℝ)
  | succ K ih =>
    simp only [Finset.sum_range_succ]
    exact ih.add ((hs.2 (K + 1) (by omega) t ht).const_mul (w (K + 1)))

private lemma weighted_sum_bound {lam : ℝ} {d : ℕ} (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} {A S0 : ℝ}
    (hw1 : w 1 = 1) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hA : 2 ≤ A) (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i)
    (hS0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ S0)
    (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ Finset.range K, w (k + 1) * s t (k + 1) ≤ (S0 + 1) * Real.exp (A * t) := by
  let Y : ℝ → ℝ := fun u => ∑ k ∈ Finset.range K, w (k + 1) * s u (k + 1)
  let Y' : ℝ → ℝ := fun u => ∑ k ∈ Finset.range K, w (k + 1) * drift lam d (s u) (k + 1)
  let g : ℝ → ℝ := fun u => (Y u + 1) * Real.exp (-A * u) - (S0 + 1)
  let g' : ℝ → ℝ := fun u => (Y' u - A * (Y u + 1)) * Real.exp (-A * u)
  have hg0 : g 0 ≤ 0 := by
    have hY0 := hS0 K
    dsimp [g, Y]
    simp only [neg_mul, mul_zero, Real.exp_zero, mul_one]
    linarith
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt g (g' u) (Set.Ici 0) u := by
    intro u hu
    have hd1 : HasDerivWithinAt (fun v => Y v + 1) (Y' u) (Set.Ici 0) u :=
      (hasDerivWithinAt_weighted_sum hs w K hu).add_const 1
    have hd2 : HasDerivWithinAt (fun v => Real.exp (-A * v))
        (Real.exp (-A * u) * (-A)) (Set.Ici 0) u := by
      have hlin : HasDerivWithinAt (fun v : ℝ => -A * v) (-A) (Set.Ici 0) u := by
        simpa using (hasDerivWithinAt_id u (Set.Ici 0)).const_mul (-A)
      exact hlin.exp
    exact ((hd1.mul hd2).congr_deriv (by ring)).sub_const (S0 + 1)
  have hsum_drift : ∀ u : ℝ, 0 ≤ u → Y' u ≤ 1 + A * Y u := by
    intro u hu
    have hst : IsState (s u) := hs.1 u hu
    dsimp [Y', Y]
    cases K with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      exact zero_le_one
    | succ m =>
      have h1 := sum_weighted_drift_le hd hlam0 hlam1 hst hw1 hw_nonneg hwA m
      have h2 : ∑ k ∈ Finset.range m, w (k + 1) * s u (k + 1) ≤
          ∑ k ∈ Finset.range (m + 1), w (k + 1) * s u (k + 1) := by
        rw [Finset.sum_range_succ]
        linarith [mul_nonneg (hw_nonneg (m + 1)) (hst.2.1 (m + 1))]
      have h3 : A * ∑ k ∈ Finset.range m, w (k + 1) * s u (k + 1) ≤
          A * ∑ k ∈ Finset.range (m + 1), w (k + 1) * s u (k + 1) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
  have hneg : ∀ u : ℝ, 0 < u → 0 < g u → g' u < 0 := by
    intro u hu _
    have hle := hsum_drift u hu.le
    dsimp [g']
    apply mul_neg_of_neg_of_pos _ (Real.exp_pos _)
    linarith
  have hle := nonpos_of_hasDerivWithinAt_neg hg0 hderiv hneg ht
  dsimp [g, Y] at hle
  have hmul : (∑ k ∈ Finset.range K, w (k + 1) * s t (k + 1) + 1) * Real.exp (-A * t) * Real.exp (A * t) ≤
      (S0 + 1) * Real.exp (A * t) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  rw [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  linarith

private lemma single_coord_weighted_bound {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} {A S0 : ℝ}
    (hw1 : w 1 = 1) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hA : 2 ≤ A) (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i)
    (hS0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ S0)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (m : ℕ) (hm : 1 ≤ m) :
    w m * s t m ≤ (S0 + 1) * Real.exp (A * T) := by
  have hsum := weighted_sum_bound hd hlam0 hlam1 hs hw1 hw_nonneg hA hwA hS0 m ht.1
  have hst : IsState (s t) := hs.1 t ht.1
  have hsingle : w m * s t m ≤ ∑ k ∈ Finset.range m, w (k + 1) * s t (k + 1) := by
    conv_rhs => rw [show m = (m - 1) + 1 by omega, Finset.sum_range_succ]
    have hrew : m - 1 + 1 = m := by omega
    rw [hrew]
    have : 0 ≤ ∑ k ∈ Finset.range (m - 1), w (k + 1) * s t (k + 1) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nonneg _) (hst.2.1 _))
    linarith
  have hS0_nonneg : 0 ≤ S0 := by
    have := hS0 0
    simpa using this
  have hexp_le : Real.exp (A * t) ≤ Real.exp (A * T) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left ht.2 (by linarith)
  calc w m * s t m ≤ ∑ k ∈ Finset.range m, w (k + 1) * s t (k + 1) := hsingle
    _ ≤ (S0 + 1) * Real.exp (A * t) := hsum
    _ ≤ (S0 + 1) * Real.exp (A * T) :=
        mul_le_mul_of_nonneg_left hexp_le (by linarith)

private lemma next_coord_weighted_bound {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} {A S0 : ℝ}
    (hw1 : w 1 = 1) (hw_ge_one : ∀ i, 1 ≤ i → 1 ≤ w i) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hA : 2 ≤ A) (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i)
    (hS0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ S0)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (m : ℕ) (hm : 1 ≤ m) :
    let BT : ℝ := (S0 + 1) * Real.exp (A * T)
    w (m + 1) * s t (m + 1) ≤ w (m + 1) * s 0 (m + 1) + ((A * BT ^ 2 + 1) * T) / w m := by
  intro BT
  have hwm_pos : 0 < w m := lt_of_lt_of_le zero_lt_one (hw_ge_one m hm)
  let rate : ℝ := (A * BT ^ 2 + 1) / w m
  let g : ℝ → ℝ := fun u =>
    if u ≤ T then w (m + 1) * s u (m + 1) - w (m + 1) * s 0 (m + 1) - rate * u
    else w (m + 1) * s T (m + 1) - w (m + 1) * s 0 (m + 1) - rate * T
  -- Even simpler: apply nonpos_of_hasDerivWithinAt_neg on [0, t] directly!
  let f : ℝ → ℝ := fun u => w (m + 1) * s u (m + 1) - w (m + 1) * s 0 (m + 1) - rate * u
  let f' : ℝ → ℝ := fun u => w (m + 1) * drift lam d (s u) (m + 1) - rate
  have hf0 : f 0 ≤ 0 := by dsimp [f]; linarith
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt f (f' u) (Set.Ici 0) u := by
    intro u hu
    have hd1 : HasDerivWithinAt (fun v => w (m + 1) * s v (m + 1) - w (m + 1) * s 0 (m + 1))
        (w (m + 1) * drift lam d (s u) (m + 1)) (Set.Ici 0) u :=
      ((hs.2 (m + 1) (by omega) u hu).const_mul (w (m + 1))).sub_const _
    have hd2 : HasDerivWithinAt (fun v : ℝ => rate * v) rate (Set.Ici 0) u := by
      simpa using (hasDerivWithinAt_id u (Set.Ici 0)).const_mul rate
    exact hd1.sub hd2
  -- Wait: in nonpos_of_hasDerivWithinAt_neg on [0, t], we only need hneg on (0, t]!
  have hcont : ContinuousOn f (Set.Icc 0 t) := by
    intro u hu
    exact ((hderiv u hu.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr ht.1) hcont with ⟨t0, ht0, hmax⟩
  have hft_le : f t ≤ f t0 := hmax (Set.right_mem_Icc.mpr ht.1)
  have hft0_nonpos : f t0 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have ht0_ne : t0 ≠ 0 := by intro h0; subst h0; linarith
    have ht0_gt : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
    have hd_nonneg : 0 ≤ f' t0 :=
      deriv_nonneg_of_max_on_Icc ht0_gt (hderiv t0 ht0.1)
        (fun u hu => hmax ⟨hu.1, hu.2.trans ht0.2⟩)
    have ht0_Icc_T : t0 ∈ Set.Icc 0 T := ⟨ht0.1, ht0.2.trans ht.2⟩
    have hwm_s_le : w m * s t0 m ≤ BT :=
      single_coord_weighted_bound hd hlam0 hlam1 hs hw1 hw_nonneg hA hwA hS0 hT ht0_Icc_T m hm
    have hst0 : IsState (s t0) := hs.1 t0 ht0.1
    have hdr_sq : drift lam d (s t0) (m + 1) ≤ s t0 m ^ 2 := by
      simpa using drift_le_prev_sq hd hlam0 hlam1 hst0 (m + 1)
    have hw_step : w (m + 1) ≤ A * w m := hwA m hm
    have hwm_s_nonneg : 0 ≤ w m * s t0 m := mul_nonneg hwm_pos.le (hst0.2.1 m)
    have hsq_le : (w m * s t0 m) ^ 2 ≤ BT ^ 2 :=
      pow_le_pow_left₀ hwm_s_nonneg hwm_s_le 2
    have hdrift_bound : w (m + 1) * drift lam d (s t0) (m + 1) < rate := by
      have h1 : w (m + 1) * drift lam d (s t0) (m + 1) ≤ (A * w m) * s t0 m ^ 2 := by
        calc w (m + 1) * drift lam d (s t0) (m + 1)
            ≤ w (m + 1) * s t0 m ^ 2 := mul_le_mul_of_nonneg_left hdr_sq (hw_nonneg _)
          _ ≤ (A * w m) * s t0 m ^ 2 := mul_le_mul_of_nonneg_right hw_step (sq_nonneg _)
      have h2 : (A * w m) * s t0 m ^ 2 = (A * (w m * s t0 m) ^ 2) / w m := by
        field_simp [hwm_pos.ne']
      have h3 : (A * (w m * s t0 m) ^ 2) / w m ≤ (A * BT ^ 2) / w m :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le (by linarith)) hwm_pos.le
      have h4 : (A * BT ^ 2) / w m < rate := by
        dsimp [rate]
        exact div_lt_div_of_pos_right (by linarith) hwm_pos
      linarith
    dsimp [f'] at hd_nonneg
    linarith
  have hft_nonpos : f t ≤ 0 := le_trans hft_le hft0_nonpos
  dsimp [f, rate] at hft_nonpos
  have hrate_nonneg : 0 ≤ (A * BT ^ 2 + 1) / w m := div_nonneg (by positivity) hwm_pos.le
  have hmul_t : ((A * BT ^ 2 + 1) / w m) * t ≤ ((A * BT ^ 2 + 1) * T) / w m := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (by positivity)) hwm_pos.le
  linarith

private lemma exists_le_div_of_sum_le {f : ℕ → ℝ} {S : ℝ} {L : ℕ} (hL : 1 ≤ L)
    (hsum : ∑ j ∈ Finset.range L, f j ≤ S) :
    ∃ j < L, f j ≤ S / (L : ℝ) := by
  by_contra h
  push_neg at h
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hlt : ∑ _j ∈ Finset.range L, (S / (L : ℝ)) < ∑ j ∈ Finset.range L, f j := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
    intro j hj
    exact h j (Finset.mem_range.mp hj)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hLpos.ne'] at hlt
  linarith

private lemma exists_cutoff_M {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} {A S0 S_pi : ℝ}
    (hw1 : w 1 = 1) (hw_ge_one : ∀ i, 1 ≤ i → 1 ≤ w i) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_mono : Monotone w)
    (hA : 2 ≤ A) (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i)
    (hS0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ S0)
    (hSpi : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1) ≤ S_pi)
    (hw_unbounded : ∀ B : ℝ, ∃ N_B : ℕ, ∀ i : ℕ, N_B ≤ i → B < w i)
    (N : ℕ) {T ε1 : ℝ} (hT : 0 ≤ T) (hε1 : 0 < ε1) :
    ∃ M : ℕ, N ≤ M ∧ ∀ t ∈ Set.Icc 0 T, w M * |s t (M + 1) - fixedPoint lam d (M + 1)| ≤ ε1 := by
  let BT : ℝ := (S0 + 1) * Real.exp (A * T)
  let B_req : ℝ := (2 * (A * BT ^ 2 + 1) * T + 1) / ε1
  obtain ⟨N_B, hN_B⟩ := hw_unbounded B_req
  let N0 : ℕ := max (max N 1) N_B
  have hN0_ge_N : N ≤ N0 := le_trans (le_max_left N 1) (le_max_left _ _)
  have hN0_ge_one : 1 ≤ N0 := le_trans (le_max_right N 1) (le_max_left _ _)
  have hN0_ge_NB : N_B ≤ N0 := le_max_right _ _
  obtain ⟨L0, hL0⟩ := exists_nat_gt ((2 * (S0 + S_pi)) / ε1)
  let L : ℕ := max L0 1
  have hL_ge_one : 1 ≤ L := le_max_right L0 1
  have hL_gt : (2 * (S0 + S_pi)) / ε1 < (L : ℝ) := by
    calc (2 * (S0 + S_pi)) / ε1 < (L0 : ℝ) := hL0
      _ ≤ (L : ℝ) := by exact_mod_cast le_max_left L0 1
  have hsum_L : ∑ j ∈ Finset.range L,
      (w (N0 + j + 1) * s 0 (N0 + j + 1) + w (N0 + j + 1) * fixedPoint lam d (N0 + j + 1)) ≤
      S0 + S_pi := by
    rw [Finset.sum_add_distrib]
    have hst0 : IsState (s 0) := hs.1 0 le_rfl
    have hsub1 : ∑ j ∈ Finset.range L, w (N0 + j + 1) * s 0 (N0 + j + 1) ≤
        ∑ k ∈ Finset.range (N0 + L), w (k + 1) * s 0 (k + 1) := by
      have hsplit := Finset.sum_range_add (fun k => w (k + 1) * s 0 (k + 1)) N0 L
      have hnonneg : 0 ≤ ∑ k ∈ Finset.range N0, w (k + 1) * s 0 (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nonneg _) (hst0.2.1 _))
      linarith
    have hsub2 : ∑ j ∈ Finset.range L, w (N0 + j + 1) * fixedPoint lam d (N0 + j + 1) ≤
        ∑ k ∈ Finset.range (N0 + L), w (k + 1) * fixedPoint lam d (k + 1) := by
      have hsplit := Finset.sum_range_add (fun k => w (k + 1) * fixedPoint lam d (k + 1)) N0 L
      have hnonneg : 0 ≤ ∑ k ∈ Finset.range N0, w (k + 1) * fixedPoint lam d (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nonneg _) (fixedPoint_nonneg hlam0 d _))
      linarith
    linarith [hS0 (N0 + L), hSpi (N0 + L)]
  obtain ⟨j, hj_lt, hj_le⟩ := exists_le_div_of_sum_le hL_ge_one hsum_L
  let M : ℕ := N0 + j
  refine ⟨M, by omega, ?_⟩
  intro t ht
  have hM_ge_one : 1 ≤ M := by omega
  have hwM_gt : B_req < w M := hN_B M (by omega)
  have hwM_pos : 0 < w M := lt_of_lt_of_le zero_lt_one (hw_ge_one M hM_ge_one)
  have htail_t : ((A * BT ^ 2 + 1) * T) / w M ≤ ε1 / 2 := by
    have h1 : (2 * (A * BT ^ 2 + 1) * T + 1) < w M * ε1 := (div_lt_iff₀ hε1).mp hwM_gt
    rw [div_le_iff₀ hwM_pos]
    linarith
  have hj_lt_ε : (S0 + S_pi) / (L : ℝ) ≤ ε1 / 2 := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
    have h1 : 2 * (S0 + S_pi) < (L : ℝ) * ε1 := (div_lt_iff₀ hε1).mp hL_gt
    rw [div_le_iff₀ hLpos]
    linarith
  have hnext := next_coord_weighted_bound hd hlam0 hlam1 hs hw1 hw_ge_one hw_nonneg hA hwA hS0 hT ht M hM_ge_one
  have hst : IsState (s t) := hs.1 t ht.1
  have habs_le : |s t (M + 1) - fixedPoint lam d (M + 1)| ≤ s t (M + 1) + fixedPoint lam d (M + 1) := by
    have htri := abs_sub (s t (M + 1)) (fixedPoint lam d (M + 1))
    rw [abs_of_nonneg (hst.2.1 _), abs_of_nonneg (fixedPoint_nonneg hlam0 d _)] at htri
    exact htri
  have hw_le_succ : w M ≤ w (M + 1) := hw_mono (Nat.le_succ M)
  calc w M * |s t (M + 1) - fixedPoint lam d (M + 1)|
      ≤ w (M + 1) * |s t (M + 1) - fixedPoint lam d (M + 1)| :=
        mul_le_mul_of_nonneg_right hw_le_succ (abs_nonneg _)
    _ ≤ w (M + 1) * (s t (M + 1) + fixedPoint lam d (M + 1)) :=
        mul_le_mul_of_nonneg_left habs_le (hw_nonneg _)
    _ = w (M + 1) * s t (M + 1) + w (M + 1) * fixedPoint lam d (M + 1) := by ring
    _ ≤ (w (M + 1) * s 0 (M + 1) + ((A * BT ^ 2 + 1) * T) / w M) +
          w (M + 1) * fixedPoint lam d (M + 1) := by linarith
    _ = (w (N0 + j + 1) * s 0 (N0 + j + 1) + w (N0 + j + 1) * fixedPoint lam d (N0 + j + 1)) +
          ((A * BT ^ 2 + 1) * T) / w M := by dsimp [M]; ring
    _ ≤ ε1 / 2 + ε1 / 2 := by linarith
    _ = ε1 := by ring

private noncomputable def psi (η x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + η ^ 2) - η

private noncomputable def psiDeriv (η x : ℝ) : ℝ :=
  x / Real.sqrt (x ^ 2 + η ^ 2)

private lemma sqrt_sq_add_sq_bounds {η : ℝ} (hη : 0 < η) (x : ℝ) :
    0 < Real.sqrt (x ^ 2 + η ^ 2) ∧
    |x| ≤ Real.sqrt (x ^ 2 + η ^ 2) ∧
    Real.sqrt (x ^ 2 + η ^ 2) ≤ |x| + η := by
  refine ⟨Real.sqrt_pos.mpr (by positivity), ?_, ?_⟩
  · rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    linarith [sq_nonneg η]
  · have hpos : 0 ≤ |x| + η := by positivity
    rw [← Real.sqrt_sq hpos]
    apply Real.sqrt_le_sqrt
    have : (|x| + η) ^ 2 = x ^ 2 + 2 * |x| * η + η ^ 2 := by
      calc (|x| + η) ^ 2 = |x| ^ 2 + 2 * |x| * η + η ^ 2 := by ring
        _ = x ^ 2 + 2 * |x| * η + η ^ 2 := by rw [sq_abs]
    rw [this]
    have : 0 ≤ 2 * |x| * η := by positivity
    linarith

private lemma psi_bounds {η : ℝ} (hη : 0 < η) (x : ℝ) :
    0 ≤ psi η x ∧ psi η x ≤ |x| ∧ |x| - η ≤ psi η x := by
  obtain ⟨_, h1, h2⟩ := sqrt_sq_add_sq_bounds hη x
  unfold psi
  have hη_le : η ≤ Real.sqrt (x ^ 2 + η ^ 2) := by
    conv_lhs => rw [← Real.sqrt_sq hη.le]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg x])
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma hasDerivWithinAt_psi {η : ℝ} (hη : 0 < η) {f : ℝ → ℝ} {f' t : ℝ}
    (hf : HasDerivWithinAt f f' (Set.Ici 0) t) :
    HasDerivWithinAt (fun u => psi η (f u)) (psiDeriv η (f t) * f') (Set.Ici 0) t := by
  unfold psi psiDeriv
  have hsq : HasDerivWithinAt (fun u => f u ^ 2 + η ^ 2) (2 * f t * f') (Set.Ici 0) t := by
    have h1 : HasDerivWithinAt (fun u => f u * f u) (f' * f t + f t * f') (Set.Ici 0) t :=
      hf.mul hf
    have h2 : (fun u => f u ^ 2 + η ^ 2) = (fun u => f u * f u + η ^ 2) := by
      ext u; ring
    rw [h2]
    exact (h1.add_const (η ^ 2)).congr_deriv (by ring)
  have hne : f t ^ 2 + η ^ 2 ≠ 0 := by positivity
  have hsqrt := (hsq.sqrt hne).sub_const η
  refine hsqrt.congr_deriv ?_
  have hr_ne : Real.sqrt (f t ^ 2 + η ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hr_ne]

private lemma psiDeriv_coord_bound {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {x : ℕ → ℝ} (hx : IsState x)
    {η : ℝ} (hη : 0 < η) (i : ℕ) (hi : 1 ≤ i) :
    let ε : ℕ → ℝ := fun j => x j - fixedPoint lam d j
    let a : ℕ → ℝ := fun j => lam * (x j ^ d - fixedPoint lam d j ^ d)
    psiDeriv η (ε i) * drift lam d x i ≤
      |a (i - 1)| - |a i| - |ε i| + |ε (i + 1)| + (cSeq lam d i + 1) * η := by
  intro ε a
  have hdr_eq : drift lam d x i = a (i - 1) - a i - ε i + ε (i + 1) := by
    have h0 := fixedPoint_drift_eq_zero lam d i hi
    have : drift lam d x i = drift lam d x i - drift lam d (fixedPoint lam d) i := by linarith
    rw [this]
    unfold drift
    dsimp [a, ε]
    ring
  rw [hdr_eq]
  let r : ℝ := Real.sqrt (ε i ^ 2 + η ^ 2)
  obtain ⟨hr_pos, habs_le_r, hr_le_abs_add⟩ := sqrt_sq_add_sq_bounds hη (ε i)
  change 0 < r at hr_pos
  change |ε i| ≤ r at habs_le_r
  change r ≤ |ε i| + η at hr_le_abs_add
  have hpsi_abs : |psiDeriv η (ε i)| ≤ 1 := by
    unfold psiDeriv
    rw [abs_div, abs_of_pos hr_pos, div_le_one hr_pos]
    exact habs_le_r
  have hterm1 : psiDeriv η (ε i) * a (i - 1) ≤ |a (i - 1)| := by
    calc psiDeriv η (ε i) * a (i - 1) ≤ |psiDeriv η (ε i) * a (i - 1)| := le_abs_self _
      _ = |psiDeriv η (ε i)| * |a (i - 1)| := abs_mul _ _
      _ ≤ 1 * |a (i - 1)| := mul_le_mul_of_nonneg_right hpsi_abs (abs_nonneg _)
      _ = |a (i - 1)| := one_mul _
  have hterm4 : psiDeriv η (ε i) * ε (i + 1) ≤ |ε (i + 1)| := by
    calc psiDeriv η (ε i) * ε (i + 1) ≤ |psiDeriv η (ε i) * ε (i + 1)| := le_abs_self _
      _ = |psiDeriv η (ε i)| * |ε (i + 1)| := abs_mul _ _
      _ ≤ 1 * |ε (i + 1)| := mul_le_mul_of_nonneg_right hpsi_abs (abs_nonneg _)
      _ = |ε (i + 1)| := one_mul _
  have h_same_sign : ε i * a i = |ε i| * |a i| := by
    dsimp [ε, a]
    rw [abs_mul, abs_of_pos hlam0]
    have h1 := mul_pow_sub_pow_eq_abs (hx.2.1 i) (fixedPoint_nonneg hlam0 d i) d
    calc (x i - fixedPoint lam d i) * (lam * (x i ^ d - fixedPoint lam d i ^ d))
        = lam * ((x i - fixedPoint lam d i) * (x i ^ d - fixedPoint lam d i ^ d)) := by ring
      _ = lam * (|x i - fixedPoint lam d i| * |x i ^ d - fixedPoint lam d i ^ d|) := by rw [h1]
      _ = |x i - fixedPoint lam d i| * (lam * |x i ^ d - fixedPoint lam d i ^ d|) := by ring
  have hai_le : |a i| ≤ cSeq lam d i * r := by
    have h1 := abs_lam_pow_sub_le_cSeq hd hlam0 hlam1 (hx.2.1 i) (isState_le_one hx i) i
    calc |a i| ≤ cSeq lam d i * |ε i| := h1
      _ ≤ cSeq lam d i * r := mul_le_mul_of_nonneg_left habs_le_r (cSeq_pos hlam0 d i).le
  have hterm2 : -psiDeriv η (ε i) * a i ≤ -|a i| + cSeq lam d i * η := by
    have hdiff : |a i| - psiDeriv η (ε i) * a i = ((r - |ε i|) * |a i|) / r := by
      unfold psiDeriv
      change |a i| - (ε i / r) * a i = ((r - |ε i|) * |a i|) / r
      rw [div_mul_eq_mul_div, h_same_sign]
      field_simp [hr_pos.ne']
    have hbound : ((r - |ε i|) * |a i|) / r ≤ cSeq lam d i * η := by
      rw [div_le_iff₀ hr_pos]
      calc (r - |ε i|) * |a i| ≤ η * |a i| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ ≤ η * (cSeq lam d i * r) :=
            mul_le_mul_of_nonneg_left hai_le hη.le
        _ = cSeq lam d i * η * r := by ring
    linarith
  have hterm3 : -psiDeriv η (ε i) * ε i ≤ -|ε i| + η := by
    have hdiff : |ε i| - psiDeriv η (ε i) * ε i = ((r - |ε i|) * |ε i|) / r := by
      unfold psiDeriv
      change |ε i| - (ε i / r) * ε i = ((r - |ε i|) * |ε i|) / r
      have hsq_abs : ε i * ε i = |ε i| * |ε i| := by
        rw [← sq, ← sq_abs, sq]
      rw [div_mul_eq_mul_div, hsq_abs]
      field_simp [hr_pos.ne']
    have hbound : ((r - |ε i|) * |ε i|) / r ≤ η := by
      rw [div_le_iff₀ hr_pos]
      calc (r - |ε i|) * |ε i| ≤ η * |ε i| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ ≤ η * r := mul_le_mul_of_nonneg_left habs_le_r hη.le
    linarith
  linarith

private lemma telescope_a (w a : ℕ → ℝ) (ha0 : a 0 = 0) :
    ∀ M : ℕ, ∑ k ∈ Finset.range M, w (k + 1) * (a k - a (k + 1)) =
      (∑ k ∈ Finset.range M, (w (k + 2) - w (k + 1)) * a (k + 1)) - w (M + 1) * a M
  | 0 => by simp [ha0]
  | M + 1 => by
    rw [Finset.sum_range_succ, telescope_a w a ha0 M, Finset.sum_range_succ]
    ring

private lemma telescope_b (w b : ℕ → ℝ) (hw0 : w 0 = 0) :
    ∀ M : ℕ, ∑ k ∈ Finset.range M, w (k + 1) * (-b (k + 1) + b (k + 2)) =
      -(∑ k ∈ Finset.range M, (w (k + 1) - w k) * b (k + 1)) + w M * b (M + 1)
  | 0 => by simp [hw0]
  | M + 1 => by
    rw [Finset.sum_range_succ, telescope_b w b hw0 M, Finset.sum_range_succ]
    ring

private lemma sum_psiDeriv_drift_bound {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {x : ℕ → ℝ} (hx : IsState x)
    {w : ℕ → ℝ} {δ η : ℝ} (hw0 : w 0 = 0) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_mono : Monotone w) (hδ_pos : 0 < δ) (hη : 0 < η)
    (h_recur : ∀ k : ℕ, cSeq lam d (k + 1) * (w (k + 2) - w (k + 1)) - (w (k + 1) - w k) ≤
      -δ * w (k + 1))
    (M : ℕ) :
    let ε : ℕ → ℝ := fun j => x j - fixedPoint lam d j
    ∑ k ∈ Finset.range M, w (k + 1) * (psiDeriv η (ε (k + 1)) * drift lam d x (k + 1)) ≤
      -δ * (∑ k ∈ Finset.range M, w (k + 1) * psi η (ε (k + 1))) +
      w M * |ε (M + 1)| +
      η * ∑ k ∈ Finset.range M, w (k + 1) * (cSeq lam d (k + 1) + 1) := by
  intro ε
  let a : ℕ → ℝ := fun j => |lam * (x j ^ d - fixedPoint lam d j ^ d)|
  let b : ℕ → ℝ := fun j => |ε j|
  have ha0 : a 0 = 0 := by
    dsimp [a]
    rw [hx.1, fixedPoint_zero, sub_self, mul_zero, abs_zero]
  have h1 : ∑ k ∈ Finset.range M, w (k + 1) * (psiDeriv η (ε (k + 1)) * drift lam d x (k + 1)) ≤
      ∑ k ∈ Finset.range M, w (k + 1) *
        (a k - a (k + 1) - b (k + 1) + b (k + 2) + (cSeq lam d (k + 1) + 1) * η) := by
    apply Finset.sum_le_sum
    intro k _
    have hcoord := psiDeriv_coord_bound hd hlam0 hlam1 hx hη (k + 1) (by omega)
    exact mul_le_mul_of_nonneg_left hcoord (hw_nonneg _)
  have hsplit : ∑ k ∈ Finset.range M, w (k + 1) *
        (a k - a (k + 1) - b (k + 1) + b (k + 2) + (cSeq lam d (k + 1) + 1) * η) =
      (∑ k ∈ Finset.range M, w (k + 1) * (a k - a (k + 1))) +
      (∑ k ∈ Finset.range M, w (k + 1) * (-b (k + 1) + b (k + 2))) +
      η * ∑ k ∈ Finset.range M, w (k + 1) * (cSeq lam d (k + 1) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit, telescope_a w a ha0 M, telescope_b w b hw0 M] at h1
  have hwM_aM_nonneg : 0 ≤ w (M + 1) * a M := mul_nonneg (hw_nonneg _) (abs_nonneg _)
  have h_comb : (∑ k ∈ Finset.range M, (w (k + 2) - w (k + 1)) * a (k + 1)) -
      (∑ k ∈ Finset.range M, (w (k + 1) - w k) * b (k + 1)) ≤
      -δ * ∑ k ∈ Finset.range M, w (k + 1) * b (k + 1) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hw_diff : 0 ≤ w (k + 2) - w (k + 1) := sub_nonneg.mpr (hw_mono (Nat.le_succ (k + 1)))
    have ha_le : a (k + 1) ≤ cSeq lam d (k + 1) * b (k + 1) :=
      abs_lam_pow_sub_le_cSeq hd hlam0 hlam1 (hx.2.1 (k + 1)) (isState_le_one hx (k + 1)) (k + 1)
    have hrec := h_recur k
    calc (w (k + 2) - w (k + 1)) * a (k + 1) - (w (k + 1) - w k) * b (k + 1)
        ≤ (w (k + 2) - w (k + 1)) * (cSeq lam d (k + 1) * b (k + 1)) -
            (w (k + 1) - w k) * b (k + 1) := by
          linarith [mul_le_mul_of_nonneg_left ha_le hw_diff]
      _ = (cSeq lam d (k + 1) * (w (k + 2) - w (k + 1)) - (w (k + 1) - w k)) * b (k + 1) := by ring
      _ ≤ (-δ * w (k + 1)) * b (k + 1) :=
          mul_le_mul_of_nonneg_right hrec (abs_nonneg _)
      _ = -δ * (w (k + 1) * b (k + 1)) := by ring
  have hpsi_le_b : ∑ k ∈ Finset.range M, w (k + 1) * psi η (ε (k + 1)) ≤
      ∑ k ∈ Finset.range M, w (k + 1) * b (k + 1) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (psi_bounds hη (ε (k + 1))).2.1 (hw_nonneg _)
  have hdelta_psi : -δ * ∑ k ∈ Finset.range M, w (k + 1) * b (k + 1) ≤
      -δ * ∑ k ∈ Finset.range M, w (k + 1) * psi η (ε (k + 1)) := by
    linarith [mul_le_mul_of_nonneg_left hpsi_le_b hδ_pos.le]
  linarith

private lemma hasDerivWithinAt_F_M {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}
    (hs : IsTrajectory lam d s) (w : ℕ → ℝ) {η : ℝ} (hη : 0 < η) (M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun u => ∑ k ∈ Finset.range M, w (k + 1) * psi η (s u (k + 1) - fixedPoint lam d (k + 1)))
      (∑ k ∈ Finset.range M,
        w (k + 1) * (psiDeriv η (s t (k + 1) - fixedPoint lam d (k + 1)) * drift lam d (s t) (k + 1)))
      (Set.Ici 0) t := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact hasDerivWithinAt_const t (Set.Ici 0) (0 : ℝ)
  | succ M ih =>
    simp only [Finset.sum_range_succ]
    have hd_sub : HasDerivWithinAt (fun u => s u (M + 1) - fixedPoint lam d (M + 1))
        (drift lam d (s t) (M + 1)) (Set.Ici 0) t :=
      (hs.2 (M + 1) (by omega) t ht).sub_const _
    exact ih.add ((hasDerivWithinAt_psi hη hd_sub).const_mul (w (M + 1)))

private lemma finite_potential_decay {lam : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s)
    {w : ℕ → ℝ} {δ A S_pi P0 : ℝ}
    (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw_ge_one : ∀ i, 1 ≤ i → 1 ≤ w i) (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_mono : Monotone w) (hδ_pos : 0 < δ) (hA : 2 ≤ A)
    (hwA : ∀ i, 1 ≤ i → w (i + 1) ≤ A * w i)
    (h_recur : ∀ k : ℕ, cSeq lam d (k + 1) * (w (k + 2) - w (k + 1)) - (w (k + 1) - w k) ≤
      -δ * w (k + 1))
    (hSpi : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1) ≤ S_pi)
    (hw_unbounded : ∀ B : ℝ, ∃ N_B : ℕ, ∀ i : ℕ, N_B ≤ i → B < w i)
    (hP0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)| ≤ P0)
    (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∑ k ∈ Finset.range N, w (k + 1) * |s T (k + 1) - fixedPoint lam d (k + 1)| ≤
      P0 * Real.exp (-δ * T) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let S0 : ℝ := P0 + S_pi
  have hS0 : ∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ S0 := by
    intro K
    have htri : ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤
        (∑ k ∈ Finset.range K, w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)|) +
        (∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have h1 : s 0 (k + 1) ≤ |s 0 (k + 1) - fixedPoint lam d (k + 1)| + fixedPoint lam d (k + 1) := by
        have := le_abs_self (s 0 (k + 1) - fixedPoint lam d (k + 1))
        linarith
      calc w (k + 1) * s 0 (k + 1)
          ≤ w (k + 1) * (|s 0 (k + 1) - fixedPoint lam d (k + 1)| + fixedPoint lam d (k + 1)) :=
            mul_le_mul_of_nonneg_left h1 (hw_nonneg _)
        _ = w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)| +
              w (k + 1) * fixedPoint lam d (k + 1) := by ring
    linarith [hP0 K, hSpi K]
  let ε1 : ℝ := (δ * ε) / 3
  have hε1_pos : 0 < ε1 := by dsimp [ε1]; positivity
  obtain ⟨M, hNM, hM_bound⟩ := exists_cutoff_M hd hlam0 hlam1 hs hw1 hw_ge_one hw_nonneg hw_mono
    hA hwA hS0 hSpi hw_unbounded N hT hε1_pos
  let CM : ℝ := ∑ k ∈ Finset.range M, w (k + 1) * (cSeq lam d (k + 1) + 1)
  let WM : ℝ := ∑ k ∈ Finset.range M, w (k + 1)
  have hCM_nonneg : 0 ≤ CM := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hw_nonneg _) (by linarith [cSeq_pos hlam0 d (k + 1)])
  have hWM_nonneg : 0 ≤ WM := Finset.sum_nonneg (fun k _ => hw_nonneg _)
  let denom : ℝ := 1 + CM / δ + WM + 1 / δ
  have hdenom_pos : 0 < denom := by dsimp [denom]; positivity
  let η : ℝ := ε / (3 * denom)
  have hη_pos : 0 < η := div_pos hε (by positivity)
  let R_err : ℝ := ε1 + η * CM + η
  have hR_err_pos : 0 < R_err := by dsimp [R_err]; positivity
  let FM : ℝ → ℝ := fun u =>
    ∑ k ∈ Finset.range M, w (k + 1) * psi η (s u (k + 1) - fixedPoint lam d (k + 1))
  let FM' : ℝ → ℝ := fun u =>
    ∑ k ∈ Finset.range M,
      w (k + 1) * (psiDeriv η (s u (k + 1) - fixedPoint lam d (k + 1)) * drift lam d (s u) (k + 1))
  let g : ℝ → ℝ := fun u =>
    FM u * Real.exp (δ * u) - P0 - (R_err / δ) * (Real.exp (δ * u) - 1)
  let g' : ℝ → ℝ := fun u =>
    (FM' u + δ * FM u - R_err) * Real.exp (δ * u)
  have hg0 : g 0 ≤ 0 := by
    have hFM0 : FM 0 ≤ P0 := by
      calc FM 0 ≤ ∑ k ∈ Finset.range M, w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (psi_bounds hη_pos _).2.1 (hw_nonneg _)
        _ ≤ P0 := hP0 M
    dsimp [g]
    simp only [mul_zero, Real.exp_zero, mul_one, sub_self]
    linarith
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt g (g' u) (Set.Ici 0) u := by
    intro u hu
    have hd_FM : HasDerivWithinAt FM (FM' u) (Set.Ici 0) u :=
      hasDerivWithinAt_F_M hs w hη_pos M hu
    have hd_exp : HasDerivWithinAt (fun v => Real.exp (δ * v))
        (Real.exp (δ * u) * δ) (Set.Ici 0) u := by
      have hlin : HasDerivWithinAt (fun v : ℝ => δ * v) δ (Set.Ici 0) u := by
        simpa using (hasDerivWithinAt_id u (Set.Ici 0)).const_mul δ
      exact hlin.exp
    have hd_prod := (hd_FM.mul hd_exp).sub_const P0
    have hd_rhs : HasDerivWithinAt (fun v => (R_err / δ) * (Real.exp (δ * v) - 1))
        ((R_err / δ) * (Real.exp (δ * u) * δ)) (Set.Ici 0) u :=
      (hd_exp.sub_const 1).const_mul (R_err / δ)
    have hcancel : (R_err / δ) * (Real.exp (δ * u) * δ) = R_err * Real.exp (δ * u) := by
      field_simp [hδ_pos.ne']
    refine (hd_prod.sub hd_rhs).congr_deriv ?_
    dsimp [g']
    rw [hcancel]
    ring
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    intro u hu
    exact ((hderiv u hu.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hcont with ⟨t0, ht0, hmax⟩
  have hgT_le : g T ≤ g t0 := hmax (Set.right_mem_Icc.mpr hT)
  have hgt0_nonpos : g t0 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have ht0_ne : t0 ≠ 0 := by intro h0; subst h0; linarith
    have ht0_gt : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
    have hd_nonneg : 0 ≤ g' t0 :=
      deriv_nonneg_of_max_on_Icc ht0_gt (hderiv t0 ht0.1)
        (fun u hu => hmax ⟨hu.1, hu.2.trans ht0.2⟩)
    have hsum_dr := sum_psiDeriv_drift_bound hd hlam0 hlam1 (hs.1 t0 ht0.1) hw0 hw_nonneg
      hw_mono hδ_pos hη_pos h_recur M
    have hM_t0 := hM_bound t0 ht0
    have hFM'_lt : FM' t0 + δ * FM t0 - R_err < 0 := by
      dsimp [FM', FM, R_err, CM] at hsum_dr ⊢
      linarith
    have hd_neg : g' t0 < 0 :=
      mul_neg_of_neg_of_pos hFM'_lt (Real.exp_pos _)
    linarith
  have hgT_nonpos : g T ≤ 0 := le_trans hgT_le hgt0_nonpos
  have hFMT_le : FM T ≤ P0 * Real.exp (-δ * T) + R_err / δ := by
    dsimp [g] at hgT_nonpos
    have hexp_ge_one : 0 ≤ (R_err / δ) * Real.exp (δ * T) - (R_err / δ) * (Real.exp (δ * T) - 1) := by
      ring_nf
      exact div_nonneg hR_err_pos.le hδ_pos.le
    have h1 : FM T * Real.exp (δ * T) ≤ P0 + (R_err / δ) * Real.exp (δ * T) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-δ * T)).le
    have hexp_cancel : Real.exp (δ * T) * Real.exp (-δ * T) = 1 := by
      rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
    calc FM T = FM T * (Real.exp (δ * T) * Real.exp (-δ * T)) := by rw [hexp_cancel, mul_one]
      _ = (FM T * Real.exp (δ * T)) * Real.exp (-δ * T) := by ring
      _ ≤ (P0 + (R_err / δ) * Real.exp (δ * T)) * Real.exp (-δ * T) := h2
      _ = P0 * Real.exp (-δ * T) + (R_err / δ) * (Real.exp (δ * T) * Real.exp (-δ * T)) := by ring
      _ = P0 * Real.exp (-δ * T) + R_err / δ := by rw [hexp_cancel, mul_one]
  have hsum_N_le_M : ∑ k ∈ Finset.range N, w (k + 1) * |s T (k + 1) - fixedPoint lam d (k + 1)| ≤
      ∑ k ∈ Finset.range M, w (k + 1) * |s T (k + 1) - fixedPoint lam d (k + 1)| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    intro k _ _
    exact mul_nonneg (hw_nonneg _) (abs_nonneg _)
  have hsum_M_le_FM : ∑ k ∈ Finset.range M, w (k + 1) * |s T (k + 1) - fixedPoint lam d (k + 1)| ≤
      FM T + η * WM := by
    dsimp [FM, WM]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have hpsi := (psi_bounds hη_pos (s T (k + 1) - fixedPoint lam d (k + 1))).2.2
    have h1 := mul_le_mul_of_nonneg_left hpsi (hw_nonneg (k + 1))
    linarith
  have herr_small : R_err / δ + η * WM ≤ ε := by
    have h1 : R_err / δ + η * WM = ε1 / δ + η * (CM / δ + 1 / δ + WM) := by
      dsimp [R_err]
      ring
    have h2 : ε1 / δ = ε / 3 := by
      dsimp [ε1]
      field_simp [hδ_pos.ne']
    have h3 : CM / δ + 1 / δ + WM ≤ denom := by
      dsimp [denom]
      linarith
    have h4 : η * (CM / δ + 1 / δ + WM) ≤ ε / 3 := by
      calc η * (CM / δ + 1 / δ + WM) ≤ η * denom :=
            mul_le_mul_of_nonneg_left h3 hη_pos.le
        _ = ε / 3 := by
          dsimp [η]
          field_simp [hdenom_pos.ne']
    linarith
  linarith

private lemma sum_range_potential_le {lam : ℝ} {d : ℕ} {w x : ℕ → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i)
    (hpot : potential lam d w x < ⊤) (K : ℕ) :
    ∑ k ∈ Finset.range K, w (k + 1) * |x (k + 1) - fixedPoint lam d (k + 1)| ≤
      (potential lam d w x).toReal := by
  let f : ℕ → ℝ≥0∞ := fun i =>
    if 1 ≤ i then ENNReal.ofReal (w i * |x i - fixedPoint lam d i|) else 0
  have hsum_le : ∑ k ∈ Finset.range K, f (k + 1) ≤ potential lam d w x := by
    unfold potential
    have hmap : ∑ k ∈ Finset.range K, f (k + 1) =
        ∑ i ∈ (Finset.range K).image (fun k => k + 1), f i := by
      rw [Finset.sum_image (fun a _ b _ hab => by omega)]
    rw [hmap]
    exact ENNReal.sum_le_tsum _
  have h_ofReal : ENNReal.ofReal
      (∑ k ∈ Finset.range K, w (k + 1) * |x (k + 1) - fixedPoint lam d (k + 1)|) =
      ∑ k ∈ Finset.range K, f (k + 1) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw_nonneg _) (abs_nonneg _))]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [f]
  rw [← h_ofReal] at hsum_le
  exact (ENNReal.ofReal_le_iff_le_toReal hpot.ne).mp hsum_le

private lemma potential_le_of_sum_range_le {lam : ℝ} {d : ℕ} {w x : ℕ → ℝ} {B : ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hB : ∀ N : ℕ, ∑ k ∈ Finset.range N, w (k + 1) * |x (k + 1) - fixedPoint lam d (k + 1)| ≤ B) :
    potential lam d w x ≤ ENNReal.ofReal B := by
  unfold potential
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  cases n with
  | zero => simp
  | succ N =>
    rw [Finset.sum_range_succ', if_neg (by omega), add_zero]
    have h_eq : ∑ k ∈ Finset.range N,
        (if 1 ≤ k + 1 then ENNReal.ofReal (w (k + 1) * |x (k + 1) - fixedPoint lam d (k + 1)|) else 0) =
        ENNReal.ofReal (∑ k ∈ Finset.range N, w (k + 1) * |x (k + 1) - fixedPoint lam d (k + 1)|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw_nonneg _) (abs_nonneg _))]
      apply Finset.sum_congr rfl
      intro k _
      rw [if_pos (by omega)]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal (hB N)

private lemma theorem_3_aux (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : ℕ → ℝ, (∀ i : ℕ, 1 ≤ i → 1 ≤ w i) ∧
      ∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s →
        (potential lam d w (s 0) < ⊤ →
          ConvergesExponentially (fun t => potential lam d w (s t))) ∧
        ((∃ j : ℕ, s 0 j = 0) →
          ConvergesExponentially (fun t => potential lam d w (s t))) := by
  obtain ⟨w, δ, A, S_pi, hw0, hw1, hw_ge_one, hw_nonneg, hw_mono, hδ_pos, hA, hSpi_pos,
    hwA, h_recur, hSpi, hw_unbounded⟩ := exists_weights lam d hd hlam0 hlam1
  refine ⟨w, hw_ge_one, ?_⟩
  intro s hs
  have h_conv_of_P0 : ∀ P0 : ℝ,
      (∀ K : ℕ, ∑ k ∈ Finset.range K, w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)| ≤ P0) →
      ConvergesExponentially (fun t => potential lam d w (s t)) := by
    intro P0 hP0
    refine ⟨δ, hδ_pos, P0, ?_⟩
    intro t ht
    apply potential_le_of_sum_range_le hw_nonneg
    intro N
    exact finite_potential_decay hd hlam0 hlam1 hs hw0 hw1 hw_ge_one hw_nonneg hw_mono
      hδ_pos hA hwA h_recur hSpi hw_unbounded hP0 N ht
  refine ⟨?_, ?_⟩
  · intro hpot
    exact h_conv_of_P0 (potential lam d w (s 0)).toReal (sum_range_potential_le hw_nonneg hpot)
  · rintro ⟨j, hj⟩
    let P0 : ℝ := (∑ k ∈ Finset.range j, w (k + 1)) + S_pi
    apply h_conv_of_P0 P0
    intro K
    have hst0 : IsState (s 0) := hs.1 0 le_rfl
    have htri : ∑ k ∈ Finset.range K, w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)| ≤
        (∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1)) +
        (∑ k ∈ Finset.range K, w (k + 1) * fixedPoint lam d (k + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have habs : |s 0 (k + 1) - fixedPoint lam d (k + 1)| ≤ s 0 (k + 1) + fixedPoint lam d (k + 1) := by
        have h := abs_sub (s 0 (k + 1)) (fixedPoint lam d (k + 1))
        rw [abs_of_nonneg (hst0.2.1 _), abs_of_nonneg (fixedPoint_nonneg hlam0 d _)] at h
        exact h
      calc w (k + 1) * |s 0 (k + 1) - fixedPoint lam d (k + 1)|
          ≤ w (k + 1) * (s 0 (k + 1) + fixedPoint lam d (k + 1)) :=
            mul_le_mul_of_nonneg_left habs (hw_nonneg _)
        _ = w (k + 1) * s 0 (k + 1) + w (k + 1) * fixedPoint lam d (k + 1) := by ring
    have hs0_bound : ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1) ≤ ∑ k ∈ Finset.range j, w (k + 1) := by
      by_cases hKj : K ≤ j
      · calc ∑ k ∈ Finset.range K, w (k + 1) * s 0 (k + 1)
            ≤ ∑ k ∈ Finset.range K, w (k + 1) * 1 := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (isState_le_one hst0 _) (hw_nonneg _)
          _ = ∑ k ∈ Finset.range K, w (k + 1) := by simp
          _ ≤ ∑ k ∈ Finset.range j, w (k + 1) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKj) (fun k _ _ => hw_nonneg _)
      · push_neg at hKj
        have hsplit : K = j + (K - j) := by omega
        rw [hsplit, Finset.sum_range_add]
        have htail_zero : ∑ x ∈ Finset.range (K - j), w (j + x + 1) * s 0 (j + x + 1) = 0 := by
          apply Finset.sum_eq_zero
          intro x _
          have hs_eq : s 0 (j + x + 1) = 0 := isState_eq_zero_of_ge hst0 hj (by omega)
          rw [hs_eq, mul_zero]
        rw [htail_zero, add_zero]
        calc ∑ k ∈ Finset.range j, w (k + 1) * s 0 (k + 1)
            ≤ ∑ k ∈ Finset.range j, w (k + 1) * 1 := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (isState_le_one hst0 _) (hw_nonneg _)
          _ = ∑ k ∈ Finset.range j, w (k + 1) := by simp
    dsimp [P0]
    linarith [hSpi K]

private lemma l1Dist_le_potential {lam : ℝ} {d : ℕ} {w x : ℕ → ℝ}
    (hw_ge_one : ∀ i : ℕ, 1 ≤ i → 1 ≤ w i) :
    l1Dist lam d x ≤ potential lam d w x := by
  unfold l1Dist potential
  apply ENNReal.tsum_le_tsum
  intro i
  split_ifs with hi
  · apply ENNReal.ofReal_le_ofReal
    calc |x i - fixedPoint lam d i| = 1 * |x i - fixedPoint lam d i| := (one_mul _).symm
      _ ≤ w i * |x i - fixedPoint lam d i| :=
          mul_le_mul_of_nonneg_right (hw_ge_one i hi) (abs_nonneg _)
  · exact le_rfl

private lemma convergesExponentially_mono {f g : ℝ → ℝ≥0∞}
    (hle : ∀ t : ℝ, f t ≤ g t) (hg : ConvergesExponentially g) :
    ConvergesExponentially f := by
  rcases hg with ⟨δ, hδ, c0, hc0⟩
  exact ⟨δ, hδ, c0, fun t ht => le_trans (hle t) (hc0 t ht)⟩

theorem solution (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : ℕ → ℝ, (∀ i : ℕ, 1 ≤ i → 1 ≤ w i) ∧
      ∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s →
        (potential lam d w (s 0) < ⊤ →
          ConvergesExponentially (fun t => l1Dist lam d (s t))) ∧
        ((∃ j : ℕ, s 0 j = 0) →
          ConvergesExponentially (fun t => l1Dist lam d (s t))) := by
  obtain ⟨w, hw_ge_one, hs_prop⟩ := theorem_3_aux lam d hd hlam0 hlam1
  refine ⟨w, hw_ge_one, ?_⟩
  intro s hs
  obtain ⟨h1, h2⟩ := hs_prop s hs
  refine ⟨fun hpot => convergesExponentially_mono (fun t => l1Dist_le_potential hw_ge_one) (h1 hpot),
    fun hj => convergesExponentially_mono (fun t => l1Dist_le_potential hw_ge_one) (h2 hj)⟩
