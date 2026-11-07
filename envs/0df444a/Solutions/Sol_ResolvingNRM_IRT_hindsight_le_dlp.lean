-- Prove2me | solution 1 for ResolvingNRM.IRT.hindsight_le_dlp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:02:16.675196+00:00
-- url     : https://prove2.me/submissions/c24f167d-f272-4263-9263-f42119725c88

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT Finset

lemma irt_hd_pmf_nonneg (μ : ℝ) (k : ℕ) : 0 ≤ poissonPMF μ k := by
  unfold poissonPMF
  have : 0 ≤ max μ 0 := le_max_right _ _
  positivity

lemma irt_hd_pmf_sum_le (μ : ℝ) (N : ℕ) : ∑ i ∈ range N, poissonPMF μ i ≤ 1 := by
  unfold poissonPMF
  have h0 : 0 ≤ max μ 0 := le_max_right _ _
  have h := Real.sum_le_exp_of_nonneg h0 N
  have : ∑ i ∈ range N, Real.exp (-max μ 0) * max μ 0 ^ i / (i.factorial : ℝ) =
      Real.exp (-max μ 0) * ∑ i ∈ range N, max μ 0 ^ i / (i.factorial : ℝ) := by
    rw [mul_sum]; congr 1; ext i; ring
  rw [this]
  calc Real.exp (-max μ 0) * ∑ i ∈ range N, max μ 0 ^ i / (i.factorial : ℝ)
      ≤ Real.exp (-max μ 0) * Real.exp (max μ 0) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma irt_hd_pmf_mean_le (μ : ℝ) (hμ : 0 ≤ μ) (N : ℕ) :
    ∑ i ∈ range N, poissonPMF μ i * (i : ℝ) ≤ μ := by
  rcases N with _ | N
  · simpa using hμ
  rw [sum_range_succ']
  have hshift : ∀ i ∈ range N, poissonPMF μ (i + 1) * ((i + 1 : ℕ) : ℝ) = μ * poissonPMF μ i := by
    intro i _
    unfold poissonPMF
    rw [max_eq_left hμ, Nat.factorial_succ]
    push_cast
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [sum_congr rfl hshift, ← mul_sum]
  simp only [CharP.cast_eq_zero, mul_zero, add_zero]
  calc μ * ∑ i ∈ range N, poissonPMF μ i ≤ μ * 1 :=
        mul_le_mul_of_nonneg_left (irt_hd_pmf_sum_le μ N) hμ
    _ = μ := mul_one μ

/-- Finite sums of a product family are bounded by the product of the one-dimensional bounds. -/
lemma irt_hd_box_bound {n : ℕ} (g : Fin n → ℕ → ℝ) (b : Fin n → ℝ) (hg : ∀ j i, 0 ≤ g j i)
    (hb : ∀ j N, ∑ i ∈ range N, g j i ≤ b j) (S : Finset (Fin n → ℕ)) :
    ∑ k ∈ S, ∏ j, g j (k j) ≤ ∏ j, b j := by
  set N := S.sup (fun k => univ.sup k) + 1 with hN
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin n => range N) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro j
    rw [mem_range]
    have h1 : k j ≤ univ.sup k := le_sup (f := k) (mem_univ j)
    have h2 : univ.sup k ≤ S.sup (fun k => univ.sup k) := le_sup (f := fun k => univ.sup k) hk
    omega
  calc ∑ k ∈ S, ∏ j, g j (k j)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : Fin n => range N), ∏ j, g j (k j) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => prod_nonneg fun j _ => hg j _)
    _ = ∏ j, ∑ i ∈ range N, g j i := (prod_univ_sum (fun _ => range N) g).symm
    _ ≤ ∏ j, b j := prod_le_prod (fun j _ => sum_nonneg fun i _ => hg j i) (fun j _ => hb j N)

lemma irt_hd_le_piValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (x : Fin m → ℝ) (y₀ y : Fin n → ℝ)
    (h1 : A *ᵥ y ≤ x) (h2 : 0 ≤ y) (h3 : y ≤ y₀) : r ⬝ᵥ y ≤ piValue A r x y₀ := by
  unfold piValue
  apply le_csSup
  · refine ⟨r ⬝ᵥ y₀, ?_⟩
    rintro v ⟨y', -, -, hy', rfl⟩
    unfold dotProduct
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hy' j) (hr j)
  · exact ⟨y, h1, h2, h3, rfl⟩

lemma irt_hd_piValue_attained {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) (x : Fin m → ℝ) (hx : 0 ≤ x) (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    ∃ z : Fin n → ℝ, A *ᵥ z ≤ x ∧ 0 ≤ z ∧ z ≤ y₀ ∧ piValue A r x y₀ = r ⬝ᵥ z := by
  set F : Set (Fin n → ℝ) := {y | A *ᵥ y ≤ x} ∩ Set.Icc 0 y₀ with hF
  have hcont : Continuous (fun y : Fin n → ℝ => A *ᵥ y) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  have hFc : IsCompact F :=
    (isCompact_Icc).inter_left (isClosed_le hcont continuous_const)
  have hFne : F.Nonempty := ⟨0, by simp [hF, hx, hy₀]⟩
  have hfc : Continuous (fun y : Fin n → ℝ => r ⬝ᵥ y) :=
    (dotProductBilin ℝ ℝ r).continuous_of_finiteDimensional
  obtain ⟨z, hzF, hzmax⟩ := hFc.exists_isMaxOn hFne hfc.continuousOn
  have hz1 : A *ᵥ z ≤ x := hzF.1
  have hz2 : 0 ≤ z := hzF.2.1
  have hz3 : z ≤ y₀ := hzF.2.2
  refine ⟨z, hz1, hz2, hz3, ?_⟩
  unfold piValue
  apply IsGreatest.csSup_eq
  refine ⟨⟨z, hz1, hz2, hz3, rfl⟩, ?_⟩
  rintro v ⟨y, h1, h2, h3, rfl⟩
  exact hzmax ⟨h1, h2, h3⟩

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j)
    (T : ℝ) (hT : 0 < T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    hindsightValue A r lam T C ≤ dlpValue A r lam T C := by
  set P : (Fin n → ℕ) → ℝ := fun k => ∏ j, poissonPMF (lam j * T) (k j) with hP
  have hP0 : ∀ k, 0 ≤ P k := fun k => prod_nonneg fun j _ => irt_hd_pmf_nonneg _ _
  have hμ : ∀ j, 0 ≤ lam j * T := fun j => (mul_pos (hlam j) hT).le
  -- total mass ≤ 1
  have hPsum : ∀ S : Finset (Fin n → ℕ), ∑ k ∈ S, P k ≤ 1 := by
    intro S
    have := irt_hd_box_bound (fun j i => poissonPMF (lam j * T) i) (fun _ => 1)
      (fun j i => irt_hd_pmf_nonneg _ _) (fun j N => irt_hd_pmf_sum_le _ N) S
    simpa using this
  -- means
  have hPmean : ∀ j0 : Fin n, ∀ S : Finset (Fin n → ℕ),
      ∑ k ∈ S, P k * (k j0 : ℝ) ≤ lam j0 * T := by
    intro j0 S
    have := irt_hd_box_bound
      (fun j i => poissonPMF (lam j * T) i * (if j = j0 then (i : ℝ) else 1))
      (fun j => if j = j0 then lam j * T else 1)
      (fun j i => mul_nonneg (irt_hd_pmf_nonneg _ _) (by split_ifs <;> positivity))
      (fun j N => by
        split_ifs with h
        · simpa using irt_hd_pmf_mean_le _ (hμ j) N
        · simpa using irt_hd_pmf_sum_le _ N) S
    have e1 : ∀ k : Fin n → ℕ, ∏ j, poissonPMF (lam j * T) (k j) *
        (if j = j0 then ((k j : ℕ) : ℝ) else 1) = P k * (k j0 : ℝ) := by
      intro k
      rw [prod_mul_distrib, prod_ite_eq' univ j0 (fun j => ((k j : ℕ) : ℝ))]
      simp [hP]
    have e2 : ∏ j, (if j = j0 then lam j * T else 1) = lam j0 * T := by
      rw [prod_ite_eq' univ j0 (fun j => lam j * T)]; simp
    simp only [e1, e2] at this
    exact this
  have hPsumm : Summable P := summable_of_sum_le hP0 hPsum
  have hPtsum : ∑' k, P k ≤ 1 := Real.tsum_le_of_sum_le hP0 hPsum
  have hmeansumm : ∀ j0, Summable (fun k => P k * (k j0 : ℝ)) := fun j0 =>
    summable_of_sum_le (fun k => mul_nonneg (hP0 k) (Nat.cast_nonneg _)) (hPmean j0)
  have hmeantsum : ∀ j0, ∑' k, P k * (k j0 : ℝ) ≤ lam j0 * T := fun j0 =>
    Real.tsum_le_of_sum_le (fun k => mul_nonneg (hP0 k) (Nat.cast_nonneg _)) (hPmean j0)
  -- maximizers
  have hex : ∀ k : Fin n → ℕ, ∃ z : Fin n → ℝ, A *ᵥ z ≤ C ∧ 0 ≤ z ∧
      z ≤ (fun j => (k j : ℝ)) ∧ piValue A r C (fun j => (k j : ℝ)) = r ⬝ᵥ z := fun k =>
    irt_hd_piValue_attained A r hr C hC _ (fun j => Nat.cast_nonneg _)
  choose z hz1 hz2 hz3 hz4 using hex
  have hzs : ∀ j, Summable (fun k => P k * z k j) := fun j =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hP0 k) (hz2 k j))
      (fun k => mul_le_mul_of_nonneg_left (hz3 k j) (hP0 k)) (hmeansumm j)
  set w : Fin n → ℝ := fun j => ∑' k, P k * z k j with hw
  have hw0 : 0 ≤ w := fun j => tsum_nonneg fun k => mul_nonneg (hP0 k) (hz2 k j)
  have hwl : ∀ j, w j ≤ lam j * T := fun j =>
    le_trans (Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hz3 k j) (hP0 k))
      (hzs j) (hmeansumm j)) (hmeantsum j)
  -- linear functionals commute with the expectation
  have hlin : ∀ a : Fin n → ℝ, ∑ j, a j * w j = ∑' k, P k * ∑ j, a j * z k j := by
    intro a
    have : ∀ k, P k * ∑ j, a j * z k j = ∑ j, a j * (P k * z k j) := by
      intro k; rw [mul_sum]; congr 1; ext j; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun j _ => (hzs j).mul_left (a j))]
    congr 1; ext j
    rw [hw]; dsimp only
    rw [tsum_mul_left]
  have hAw : ∀ l, (A *ᵥ w) l ≤ C l := by
    intro l
    have e : (A *ᵥ w) l = ∑' k, P k * (A *ᵥ z k) l := by
      simp only [mulVec, dotProduct]; exact hlin (fun j => A l j)
    rw [e]
    have hs1 : Summable (fun k => P k * (A *ᵥ z k) l) := by
      have : (fun k => P k * (A *ᵥ z k) l) = fun k => ∑ j, A l j * (P k * z k j) := by
        ext k; simp only [mulVec, dotProduct]; rw [mul_sum]; congr 1; ext j; ring
      rw [this]; exact summable_sum fun j _ => (hzs j).mul_left _
    calc ∑' k, P k * (A *ᵥ z k) l ≤ ∑' k, P k * C l :=
          Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hz1 k l) (hP0 k)) hs1
            (hPsumm.mul_right _)
      _ = (∑' k, P k) * C l := tsum_mul_right
      _ ≤ 1 * C l := mul_le_mul_of_nonneg_right hPtsum (hC l)
      _ = C l := one_mul _
  have hrw : r ⬝ᵥ w = hindsightValue A r lam T C := by
    unfold hindsightValue
    rw [dotProduct, hlin r]
    congr 1; ext k
    rw [hz4 k, dotProduct]
  -- feasibility of w / T for the DLP
  have hfeas := irt_hd_le_piValue A r hr (fun l => C l / T) lam (T⁻¹ • w)
    (by
      intro l
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      show T⁻¹ * (A *ᵥ w) l ≤ C l / T
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hAw l) (inv_nonneg.mpr hT.le))
    (fun j => by
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact mul_nonneg (inv_nonneg.mpr hT.le) (hw0 j))
    (fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_le_iff₀ hT]; linarith [hwl j])
  rw [← hrw]
  unfold dlpValue
  rw [dotProduct_smul, smul_eq_mul] at hfeas
  have : r ⬝ᵥ w = T * (T⁻¹ * r ⬝ᵥ w) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hfeas hT.le
