-- Prove2me | solution 2 for RestrictedAP.Counting.theorem_5_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:25.113098+00:00
-- url     : https://prove2.me/submissions/fa707c40-8058-4463-801e-f9d2f089f603
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RestrictedAP_Counting_theorem_A_1_real
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder BigOperators

private lemma measure_map_pi {ι : Type} [Fintype ι] {α β : ι → Type}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i → β i) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).map (f i))] :
    (Measure.pi μ).map (fun z i => f i (z i)) = Measure.pi (fun i => (μ i).map (f i)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (fun z i => f i (z i)) ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => f i ⁻¹' s i) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi]
  rw [hpre, Measure.pi_pi]
  congr 1
  funext i
  rw [Measure.map_apply (hf i) (hs i)]

private lemma gaussianReal_half_normalize : (gaussianReal 0 (1 / 2 : NNReal)).map (fun x : ℝ => Real.sqrt 2 * x) = gaussianReal 0 1 := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

private lemma complexGaussian_pair :
    BraneBrauer.Orthogonal.complexGaussian.map
      (fun z : ℂ => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  unfold BraneBrauer.Orthogonal.complexGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun z : ℂ => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im)) ∘
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) =
      Prod.map (fun x : ℝ => Real.sqrt 2 * x) (fun x : ℝ => Real.sqrt 2 * x) := by
    funext p
    simp [Prod.map]
  rw [hfun, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_half_normalize]

private lemma sum_re {α : Type} [Fintype α] (g : α → ℂ) :
    (∑ a, g a).re = ∑ a, (g a).re := by
  change Complex.reLm (∑ a, g a) = _
  exact map_sum _ _ _

private lemma sum_im {α : Type} [Fintype α] (g : α → ℂ) :
    (∑ a, g a).im = ∑ a, (g a).im := by
  change Complex.imLm (∑ a, g a) = _
  exact map_sum _ _ _

private def realifyVec {I K : Type} (z : I × K → ℂ) : I × (K ⊕ K) → ℝ
  | (i, Sum.inl k) => Real.sqrt 2 * (z (i, k)).re
  | (i, Sum.inr k) => Real.sqrt 2 * (z (i, k)).im

private def pairPiToSumPi {I K : Type} (w : I × K → ℝ × ℝ) : I × (K ⊕ K) → ℝ
  | (i, Sum.inl k) => (w (i, k)).1
  | (i, Sum.inr k) => (w (i, k)).2

private def complexifyVec {I K : Type} (w : I × (K ⊕ K) → ℝ) : I × K → ℂ :=
  fun q => ((w (q.1, Sum.inl q.2) : ℂ) + (w (q.1, Sum.inr q.2) : ℂ) * Complex.I) / Real.sqrt 2

private def complexifyPart {K : Type} (w : K ⊕ K → ℝ) : K → ℂ :=
  fun k => ((w (Sum.inl k) : ℂ) + (w (Sum.inr k) : ℂ) * Complex.I) / Real.sqrt 2

private def realifyMat {I K : Type} (A : Matrix (I × K) (I × K) ℂ) :
    Matrix (I × (K ⊕ K)) (I × (K ⊕ K)) ℝ
  | (i, Sum.inl k), (i', Sum.inl k') => (A (i, k) (i', k')).re
  | (i, Sum.inl k), (i', Sum.inr k') => -(A (i, k) (i', k')).im
  | (i, Sum.inr k), (i', Sum.inl k') => (A (i, k) (i', k')).im
  | (i, Sum.inr k), (i', Sum.inr k') => (A (i, k) (i', k')).re

private def cquad {J : Type} [Fintype J] (H : Matrix J J ℂ) (z : J → ℂ) : ℂ :=
  ∑ i, ∑ j, star (z i) * H i j * z j

private def rquad {J : Type} [Fintype J] (R : Matrix J J ℝ) (w : J → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * R i j * w j

private lemma finsupp_csum {J : Type} [Fintype J] (x : J →₀ ℂ) (H : Matrix J J ℂ) :
    x.sum (fun i xi => x.sum (fun j xj => star xi * H i j * xj)) =
      ∑ i, ∑ j, star (x i) * H i j * x j := by
  rw [Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finsupp.sum_fintype]
    intro j
    simp
  · intro i
    simp

private lemma finsupp_rsum {J : Type} [Fintype J] (x : J →₀ ℝ) (H : Matrix J J ℝ) :
    x.sum (fun i xi => x.sum (fun j xj => star xi * H i j * xj)) =
      ∑ i, ∑ j, star (x i) * H i j * x j := by
  rw [Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finsupp.sum_fintype]
    intro j
    simp
  · intro i
    simp

private lemma complexifyVec_realifyVec {I K : Type} (z : I × K → ℂ) : complexifyVec (realifyVec z) = z := by
  funext ⟨i, k⟩
  apply Complex.ext <;> simp [complexifyVec, realifyVec]

private lemma realifyVec_complexifyVec {I K : Type} (w : I × (K ⊕ K) → ℝ) : realifyVec (complexifyVec w) = w := by
  funext ⟨i, k⟩
  cases k <;> simp [complexifyVec, realifyVec] <;> field_simp [Real.sqrt_ne_zero']

private lemma part_realifyVec {I n : ℕ} (j : Fin I) (g : Fin I × Fin n → ℂ) :
    complexifyPart (fun k => realifyVec g (j, k)) = (fun k => g (j, k)) := by
  funext k
  cases k <;> apply Complex.ext <;> simp [complexifyPart, realifyVec]

private lemma measurable_realifyVec {I K : Type} : Measurable (@realifyVec I K) := by
  apply measurable_pi_lambda
  rintro ⟨i, k⟩
  cases k <;> simp only [realifyVec] <;> fun_prop

private lemma measurable_pairPiToSumPi {I K : Type} : Measurable (@pairPiToSumPi I K) := by
  apply measurable_pi_lambda
  rintro ⟨i, k⟩
  cases k <;> simp only [pairPiToSumPi] <;> fun_prop

private lemma map_pairPiToSumPi {I K : Type} [Fintype I] [Fintype K]
    (μ : I × K → Measure (ℝ × ℝ)) [∀ q, SigmaFinite (μ q)]
    (ν : I × (K ⊕ K) → Measure ℝ) [∀ r, SigmaFinite (ν r)]
    (hμ : ∀ q s t, MeasurableSet s → MeasurableSet t →
      μ q (s ×ˢ t) = ν (q.1, Sum.inl q.2) s * ν (q.1, Sum.inr q.2) t) :
    (Measure.pi μ).map pairPiToSumPi = Measure.pi ν := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_pairPiToSumPi (MeasurableSet.univ_pi hs)]
  have hpre : pairPiToSumPi ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun q => s (q.1, Sum.inl q.2) ×ˢ s (q.1, Sum.inr q.2)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h q
      exact ⟨h (q.1, Sum.inl q.2), h (q.1, Sum.inr q.2)⟩
    · intro h r
      rcases r with ⟨i, k⟩
      cases k with
      | inl k => exact (h (i, k)).1
      | inr k => exact (h (i, k)).2
  rw [hpre, Measure.pi_pi]
  simp only [hμ _ _ _ (hs _) (hs _), Fintype.prod_prod_type, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]

private lemma measurable_complexifyVec {I K : Type} : Measurable (@complexifyVec I K) := by
  apply measurable_pi_lambda
  intro q
  simp only [complexifyVec]
  fun_prop

private lemma measurable_complexifyPart {K : Type} : Measurable (@complexifyPart K) := by
  apply measurable_pi_lambda
  intro k
  simp only [complexifyPart]
  fun_prop

private lemma realifyVec_mulVec {I K : Type} [Fintype I] [Fintype K] (A : Matrix (I × K) (I × K) ℂ)
    (z : I × K → ℂ) : realifyVec (A.mulVec z) = (realifyMat A).mulVec (realifyVec z) := by
  funext ⟨i, k⟩
  cases k with
  | inl k =>
      simp only [realifyVec, realifyMat, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fintype.sum_sum_type, sum_re, Complex.mul_re, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
  | inr k =>
      simp only [realifyVec, realifyMat, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fintype.sum_sum_type, sum_im, Complex.mul_im, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

private lemma realifyMat_mul {I K : Type} [Fintype I] [Fintype K] (A B : Matrix (I × K) (I × K) ℂ) :
    realifyMat (A * B) = realifyMat A * realifyMat B := by
  funext ⟨i, k⟩ ⟨i', k'⟩
  cases k with
  | inl k =>
    cases k' with
    | inl k' =>
      simp only [realifyMat, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        sum_re, Complex.mul_re]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    | inr k' =>
      simp only [realifyMat, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        sum_im, Complex.mul_im]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
  | inr k =>
    cases k' with
    | inl k' =>
      simp only [realifyMat, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        sum_im, Complex.mul_im]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    | inr k' =>
      simp only [realifyMat, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        sum_re, Complex.mul_re]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

private lemma realifyMat_conjTranspose {I K : Type} (A : Matrix (I × K) (I × K) ℂ) :
    realifyMat A.conjTranspose = (realifyMat A).transpose := by
  funext ⟨i, k⟩ ⟨i', k'⟩
  cases k <;> cases k' <;> simp [realifyMat, Matrix.conjTranspose_apply, Matrix.transpose_apply]

private lemma realifyMat_one {I K : Type} [DecidableEq I] [DecidableEq K] :
    realifyMat (1 : Matrix (I × K) (I × K) ℂ) = 1 := by
  funext ⟨i, k⟩ ⟨i', k'⟩
  cases k <;> cases k' <;> by_cases h : i = i' <;>
    simp [realifyMat, Matrix.one_apply, h, Prod.ext_iff] <;> split_ifs <;> simp_all

private lemma realifyMat_sub {I K : Type} (A B : Matrix (I × K) (I × K) ℂ) :
    realifyMat (A - B) = realifyMat A - realifyMat B := by
  funext ⟨i, k⟩ ⟨i', k'⟩
  cases k <;> cases k' <;> simp [realifyMat] <;> ring

private lemma realifyMat_real_smul {I K : Type} (c : ℝ) (A : Matrix (I × K) (I × K) ℂ) :
    realifyMat ((c : ℂ) • A) = c • realifyMat A := by
  funext ⟨i, k⟩ ⟨i', k'⟩
  cases k <;> cases k' <;> simp [realifyMat]

private lemma cPosSemidef_iff {J : Type} [Fintype J] (H : Matrix J J ℂ) :
    H.PosSemidef ↔ H.IsHermitian ∧ ∀ z : J → ℂ, 0 ≤ cquad H z := by
  constructor
  · intro h
    refine ⟨h.isHermitian, ?_⟩
    intro z
    have hz := h.2 (Finsupp.equivFunOnFinite.symm z)
    rw [finsupp_csum] at hz
    simpa only [cquad, Finsupp.equivFunOnFinite_symm_apply_apply] using hz
  · rintro ⟨hh, hq⟩
    refine ⟨hh, ?_⟩
    intro z
    rw [finsupp_csum]
    simpa only [cquad] using hq (fun i => z i)

private lemma rPosSemidef_iff {J : Type} [Fintype J] (R : Matrix J J ℝ) :
    R.PosSemidef ↔ R.IsHermitian ∧ ∀ w : J → ℝ, 0 ≤ rquad R w := by
  constructor
  · intro h
    refine ⟨h.isHermitian, ?_⟩
    intro w
    have hw := h.2 (Finsupp.equivFunOnFinite.symm w)
    rw [finsupp_rsum] at hw
    simpa only [rquad, Finsupp.equivFunOnFinite_symm_apply_apply, star_trivial] using hw
  · rintro ⟨hh, hq⟩
    refine ⟨hh, ?_⟩
    intro w
    rw [finsupp_rsum]
    simpa only [rquad, star_trivial] using hq (fun i => w i)

private lemma realifyMat_isHermitian {I K : Type} {A : Matrix (I × K) (I × K) ℂ}
    (hA : A.IsHermitian) : (realifyMat A).IsHermitian := by
  change (realifyMat A).transpose = realifyMat A
  rw [← realifyMat_conjTranspose, hA]

private lemma quad_re {I K : Type} [Fintype I] [Fintype K] (H : Matrix (I × K) (I × K) ℂ)
    (z : I × K → ℂ) : rquad (realifyMat H) (realifyVec z) = 2 * (cquad H z).re := by
  simp only [rquad, cquad, Fintype.sum_prod_type, Fintype.sum_sum_type, sum_re]
  simp only [realifyVec, realifyMat, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i' _
  apply Finset.sum_congr rfl
  intro k' _
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    _ = Real.sqrt 2 ^ 2 *
        ((z (i, k)).re * (H (i, k) (i', k')).re * (z (i', k')).re -
          (z (i, k)).re * (H (i, k) (i', k')).im * (z (i', k')).im +
          (z (i, k)).im * (H (i, k) (i', k')).im * (z (i', k')).re +
          (z (i, k)).im * (H (i, k) (i', k')).re * (z (i', k')).im) := by ring
    _ = 2 * (((z (i, k)).re * (H (i, k) (i', k')).re * (z (i', k')).re -
          (z (i, k)).re * (H (i, k) (i', k')).im * (z (i', k')).im +
          (z (i, k)).im * (H (i, k) (i', k')).im * (z (i', k')).re +
          (z (i, k)).im * (H (i, k) (i', k')).re * (z (i', k')).im)) := by rw [hs]
    _ = _ := by ring

private lemma posSemidef_realifyMat {I K : Type} [Fintype I] [Fintype K]
    {H : Matrix (I × K) (I × K) ℂ} (hH : H.PosSemidef) : (realifyMat H).PosSemidef := by
  rw [rPosSemidef_iff]
  refine ⟨realifyMat_isHermitian hH.isHermitian, ?_⟩
  intro w
  have hq := (cPosSemidef_iff H).1 hH |>.2 (complexifyVec w)
  rw [Complex.le_def] at hq
  have hq' := quad_re H (complexifyVec w)
  rw [realifyVec_complexifyVec] at hq'
  rw [hq']
  exact mul_nonneg (by norm_num) hq.1

/-- **Theorem 5.11** (p. 31), reduced to the real Gaussian reverse hypercontractivity theorem. -/
theorem solution (ℓ n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η)
    (A : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (hblock : ∀ (j : Fin ℓ) (k k' : Fin n),
      (A * A.conjTranspose) (j, k) (j, k') = if k = k' then 1 else 0)
    (hcov : (A * A.conjTranspose - (η : ℂ) • (1 : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)).PosSemidef)
    (f : Fin ℓ → (Fin n → ℂ) → ℝ) (hf : ∀ j, Measurable (f j))
    (hf01 : ∀ j z, 0 ≤ f j z ∧ f j z ≤ 1) :
    let lawG : Measure (Fin ℓ × Fin n → ℂ) :=
      (Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian)).map
        (fun z => A.mulVec z)
    (∏ j, ∫ g, f j (fun k => g (j, k)) ∂lawG) ^ (1 / η) ≤
      ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG := by
  haveI : NeZero n := ⟨by omega⟩
  let ι := Fin n ⊕ Fin n
  let B : Matrix (Fin ℓ × ι) (Fin ℓ × ι) ℝ := realifyMat A
  let lawC : Measure (Fin ℓ × Fin n → ℂ) :=
    Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian)
  let lawR : Measure (Fin ℓ × (Fin n ⊕ Fin n) → ℝ) :=
    Measure.pi (fun _ : Fin ℓ × ι => gaussianReal 0 1)
  let lawG : Measure (Fin ℓ × Fin n → ℂ) := lawC.map A.mulVec
  let law : Measure (Fin ℓ × ι → ℝ) := lawR.map B.mulVec
  change (∏ j, ∫ g, f j (fun k => g (j, k)) ∂lawG) ^ (1 / η) ≤
    ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG
  have hAmul : Measurable (fun z : Fin ℓ × Fin n → ℂ => A.mulVec z) := by fun_prop
  have hmul : B * B.transpose = realifyMat (A * A.conjTranspose) := by
    rw [← realifyMat_conjTranspose, ← realifyMat_mul]
  have hblock' : ∀ (j : Fin ℓ) (k k' : ι),
      (B * B.transpose) (j, k) (j, k') = if k = k' then 1 else 0 := by
    intro j k k'
    cases k with
    | inl k =>
      cases k' with
      | inl k' =>
        rw [hmul]
        simp only [realifyMat]
        rw [hblock]
        have hs : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inl k' ↔ k ≠ k' := by
          constructor
          · intro h hk
            exact h (congrArg Sum.inl hk)
          · intro h he
            exact h (Sum.inl.inj he)
        by_cases h : k = k'
        · subst k'
          simp
        · rw [if_neg h]
          simp only [Complex.zero_re, if_neg (hs.mpr h)]
      | inr k' =>
        rw [hmul]
        simp only [realifyMat]
        rw [hblock]
        by_cases h : k = k' <;> simp [h]
    | inr k =>
      cases k' with
      | inl k' =>
        rw [hmul]
        simp only [realifyMat]
        rw [hblock]
        by_cases h : k = k' <;> simp [h]
      | inr k' =>
        rw [hmul]
        simp only [realifyMat]
        rw [hblock]
        have hs : (Sum.inr k : Fin n ⊕ Fin n) ≠ Sum.inr k' ↔ k ≠ k' := by
          constructor
          · intro h hk
            exact h (congrArg Sum.inr hk)
          · intro h he
            exact h (Sum.inr.inj he)
        by_cases h : k = k'
        · subst k'
          simp
        · rw [if_neg h]
          simp only [Complex.zero_re, if_neg (hs.mpr h)]
  have hcov' : (B * B.transpose - η • (1 : Matrix (Fin ℓ × ι) (Fin ℓ × ι) ℝ)).PosSemidef := by
    rw [hmul, ← realifyMat_one, ← realifyMat_real_smul, ← realifyMat_sub]
    exact posSemidef_realifyMat hcov
  have hreal : lawC.map realifyVec = lawR := by
    haveI hcg : SigmaFinite BraneBrauer.Orthogonal.complexGaussian := by
      unfold BraneBrauer.Orthogonal.complexGaussian
      infer_instance
    haveI hmap : ∀ _q : Fin ℓ × Fin n, SigmaFinite (BraneBrauer.Orthogonal.complexGaussian.map
        (fun z : ℂ => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im))) := by
      intro q
      rw [complexGaussian_pair]
      infer_instance
    dsimp only [lawC, lawR]
    rw [show (@realifyVec (Fin ℓ) (Fin n)) = pairPiToSumPi ∘
        (fun z q => (Real.sqrt 2 * (z q).re, Real.sqrt 2 * (z q).im)) from by
      funext z q
      rcases q with ⟨i, k⟩
      cases k <;> rfl]
    rw [← Measure.map_map measurable_pairPiToSumPi (by fun_prop)]
    have hpi : (Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian)).map
        (fun z q => (Real.sqrt 2 * (z q).re, Real.sqrt 2 * (z q).im)) =
        Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian.map
          (fun z : ℂ => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im))) := by
      exact @measure_map_pi (Fin ℓ × Fin n) _ (fun _ => ℂ) (fun _ => ℝ × ℝ) _ _
        (fun _ => BraneBrauer.Orthogonal.complexGaussian) (fun _ => hcg)
        (fun _ z => (Real.sqrt 2 * z.re, Real.sqrt 2 * z.im)) (fun _ => by fun_prop) hmap
    rw [hpi]
    simp only [complexGaussian_pair]
    exact map_pairPiToSumPi _ _ (fun q s t hs ht => Measure.prod_prod s t)
  have hback : lawR.map complexifyVec = lawC := by
    rw [← hreal, Measure.map_map measurable_complexifyVec measurable_realifyVec]
    rw [show complexifyVec ∘ realifyVec = id from funext complexifyVec_realifyVec,
      Measure.map_id]
  have hlaw : law = lawG.map realifyVec := by
    change lawR.map B.mulVec = (lawC.map A.mulVec).map realifyVec
    rw [show lawC = lawR.map complexifyVec from hback.symm,
      Measure.map_map hAmul measurable_complexifyVec,
      Measure.map_map measurable_realifyVec (hAmul.comp measurable_complexifyVec)]
    apply congrArg (fun F => lawR.map F)
    funext w
    simp only [Function.comp_apply]
    change (realifyMat A).mulVec w = realifyVec (A.mulVec (complexifyVec w))
    calc
      (realifyMat A).mulVec w = (realifyMat A).mulVec (realifyVec (complexifyVec w)) := by
        rw [realifyVec_complexifyVec]
      _ = _ := (realifyVec_mulVec A (complexifyVec w)).symm
  let F : Fin ℓ → (ι → ℝ) → ℝ := fun j w => f j (complexifyPart w)
  have hF : ∀ j, Measurable (F j) := fun j => (hf j).comp measurable_complexifyPart
  have hF01 : ∀ j w, 0 ≤ F j w ∧ F j w ≤ 1 := fun j w => hf01 j (complexifyPart w)
  have hRH := RestrictedAP.Counting.theorem_A_1_real ℓ ι η hη B hblock' hcov' F hF hF01
  change (∏ j, ∫ w, F j (fun k => w (j, k)) ∂law) ^ (1 / η) ≤
    ∫ w, ∏ j, F j (fun k => w (j, k)) ∂law at hRH
  have hH : ∀ j, Measurable (fun w : Fin ℓ × ι → ℝ => F j (fun k => w (j, k))) := by
    intro j
    exact (hF j).comp (by fun_prop)
  have hprod : Measurable (fun w : Fin ℓ × ι → ℝ => ∏ j, F j (fun k => w (j, k))) := by
    simpa using Finset.measurable_prod Finset.univ (fun j (_ : j ∈ Finset.univ) => hH j)
  have hint (j : Fin ℓ) : ∫ w, F j (fun k => w (j, k)) ∂law =
      ∫ g, f j (fun k => g (j, k)) ∂lawG := by
    rw [hlaw, integral_map measurable_realifyVec.aemeasurable (hH j).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with g
    change f j (complexifyPart (fun k => realifyVec g (j, k))) = f j (fun k => g (j, k))
    rw [part_realifyVec]
  have hintprod : ∫ w, ∏ j, F j (fun k => w (j, k)) ∂law =
      ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG := by
    rw [hlaw, integral_map measurable_realifyVec.aemeasurable hprod.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with g
    apply Finset.prod_congr rfl
    intro j _
    change f j (complexifyPart (fun k => realifyVec g (j, k))) = f j (fun k => g (j, k))
    rw [part_realifyVec]
  calc
    (∏ j, ∫ g, f j (fun k => g (j, k)) ∂lawG) ^ (1 / η) =
        (∏ j, ∫ w, F j (fun k => w (j, k)) ∂law) ^ (1 / η) := by
      congr 1
      exact Finset.prod_congr rfl (fun j _ => (hint j).symm)
    _ ≤ ∫ w, ∏ j, F j (fun k => w (j, k)) ∂law := hRH
    _ = _ := hintprod
