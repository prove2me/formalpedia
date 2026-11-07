-- Prove2me | solution 1 for PrescAnalytics.KNN.theorem_5_knn_unbounded_case
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:23:20.011958+00:00
-- url     : https://prove2.me/submissions/ee49523a-48a9-4ee5-ad14-818a3cf251bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic
import Theorems.Thm_PrescAnalytics_KNN_walk_knn_strong_consistency
import Theorems.Thm_PrescAnalytics_KNN_lemma_6_bounded_case

open MeasureTheory ProbabilityTheory Filter Topology

theorem knn_exists_meas_version {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (f : Y → ℝ)
    (hf : AEStronglyMeasurable (fun p => f p.2) μ) :
    ∃ h : Y → ℝ, Measurable h ∧ ∀ᵐ p ∂μ, h p.2 = f p.2 := by
  set μ' : Measure (Y × X) := μ.map Prod.swap with hμ'
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  set g : X × Y → ℝ := hf.mk _ with hg
  have hgm : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hgae : ∀ᵐ p ∂μ, f p.2 = g p := hf.ae_eq_mk
  let g' : Y × X → ℝ := fun q => g q.swap
  have hg'm : StronglyMeasurable g' := hgm.comp_measurable measurable_swap
  refine ⟨fun y => ∫ x, g' (y, x) ∂(μ'.condKernel y),
    (hg'm.integral_kernel_prod_right' (κ := μ'.condKernel)).measurable, ?_⟩
  have h1 : ∀ᵐ q ∂μ', f q.1 = g' q := by
    rw [hμ', (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding.ae_map_iff (f := Prod.swap)]
    exact hgae
  have h1' : ∀ᵐ q ∂(μ'.fst ⊗ₘ μ'.condKernel), f q.1 = g' q := by
    rw [Measure.disintegrate]; exact h1
  have h2 := Measure.ae_ae_of_ae_compProd h1'
  have h3 : ∀ᵐ y ∂μ'.fst, ∫ x, g' (y, x) ∂(μ'.condKernel y) = f y := by
    filter_upwards [h2] with y hy
    rw [integral_congr_ae (hy.mono fun x hx => hx.symm)]
    simp
  have h4 : ∀ᵐ y ∂(μ.map Prod.snd), ∫ x, g' (y, x) ∂(μ'.condKernel y) = f y := by
    have : μ'.fst = μ.map Prod.snd := by rw [hμ', Measure.fst_map_swap]; rfl
    rw [← this]; exact h3
  exact ae_of_ae_map measurable_snd.aemeasurable h4

open PrescAnalytics.KNN in
theorem knn_card_rank_lt {dx : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin dx))
    (x : EuclideanSpace ℝ (Fin dx)) (N k : ℕ) (hk : k ≤ N) :
    ((Finset.range N).filter fun i => knnRank xs x N i < k).card = k := by
  classical
  set d : ℕ → ℝ := fun j => dist x (xs j) with hd
  let R : ℕ → ℕ → Prop := fun j i => d j < d i ∨ (d j = d i ∧ j < i)
  have hR_irrefl : ∀ i, ¬ R i i := by
    intro i h; rcases h with h | h
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h.2
  have hR_trans : ∀ a b e, R a b → R b e → R a e := by
    intro a b e h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2.1 ▸ h1)
    · exact Or.inl (h1.1 ▸ h2)
    · exact Or.inr ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hR_tri : ∀ a b, a ≠ b → R a b ∨ R b a := by
    intro a b hab
    rcases lt_trichotomy (d a) (d b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_or_gt_of_ne hab with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  have hrank : ∀ i, knnRank xs x N i = ((Finset.range N).filter fun j => R j i).card := by
    intro i; rfl
  -- strict monotonicity
  have hmono : ∀ a b, a < N → R a b → knnRank xs x N a < knnRank xs x N b := by
    intro a b ha hab
    rw [hrank, hrank]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha, hab⟩
      · simp only [Finset.mem_filter, Finset.mem_range, not_and]; intro _; exact hR_irrefl a
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hj.1, hR_trans _ _ _ hj.2 hab⟩
  have hinj : Set.InjOn (knnRank xs x N) (Finset.range N : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases hR_tri a b hne with h | h
    · exact absurd hab (ne_of_lt (hmono a b ha h))
    · exact absurd hab.symm (ne_of_lt (hmono b a hb h))
  have hlt : ∀ i, i < N → knnRank xs x N i < N := by
    intro i hi
    rw [hrank]
    calc ((Finset.range N).filter fun j => R j i).card
        < (Finset.range N).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
          exact ⟨i, Finset.mem_range.mpr hi, by
            simp only [Finset.mem_filter, not_and]; intro _; exact hR_irrefl i⟩
      _ = N := Finset.card_range N
  have himage : (Finset.range N).image (knnRank xs x N) = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
      obtain ⟨i, hi, rfl⟩ := hr
      exact hlt i hi
    · rw [Finset.card_image_of_injOn hinj]
  have : ((Finset.range N).filter fun i => knnRank xs x N i < k).image (knnRank xs x N)
      = Finset.range k := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨_, hik⟩, rfl⟩; exact hik
    · intro hr
      have : r ∈ (Finset.range N).image (knnRank xs x N) := by
        rw [himage]; exact Finset.mem_range.mpr (lt_of_lt_of_le hr hk)
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp this
      exact ⟨i, ⟨Finset.mem_range.mp hi, hr⟩, rfl⟩
  have hc := Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr
    (Finset.filter_subset (fun i => knnRank xs x N i < k) (Finset.range N))))
  rw [this, Finset.card_range] at hc
  exact hc.symm

open PrescAnalytics.KNN in
theorem knn_weights_good {dx : ℕ} (C δ : ℝ) (hC : 0 < C) (xs : ℕ → EuclideanSpace ℝ (Fin dx))
    (x : EuclideanSpace ℝ (Fin dx)) :
    ∀ᶠ N in atTop, (∀ i < N, 0 ≤ knnWeight C δ xs x N i) ∧
      ∑ i ∈ Finset.range N, knnWeight C δ xs x N i = 1 := by
  classical
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hkpos : 1 ≤ kSeq C δ N := by
    unfold kSeq
    apply le_min
    · rw [Nat.one_le_ceil_iff]
      exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) δ)
    · omega
  have hkN : kSeq C δ N ≤ N := by unfold kSeq; omega
  refine ⟨fun i _ => ?_, ?_⟩
  · unfold knnWeight knnWeightK
    split_ifs <;> positivity
  · unfold knnWeight knnWeightK
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hfil : (Finset.range N).filter (fun i => IsKNN (kSeq C δ N) xs x N i) =
        (Finset.range N).filter (fun i => knnRank xs x N i < kSeq C δ N) := by
      ext i; rw [Finset.mem_filter, Finset.mem_filter]; unfold IsKNN
      constructor
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Finset.mem_range.mp h1, h2⟩
    rw [hfil, knn_card_rank_lt xs x N _ hkN]
    have : (kSeq C δ N : ℝ) ≠ 0 := by exact_mod_cast (by omega : kSeq C δ N ≠ 0)
    field_simp

open PrescAnalytics.KNN in
theorem knn_wc_diff {dy dz : ℕ} (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Ys : Set (EuclideanSpace ℝ (Fin dy))) (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (N : ℕ) (z z' : EuclideanSpace ℝ (Fin dz)) (e : ℝ)
    (hnn : ∀ i < N, 0 ≤ w N i) (hsum : ∑ i ∈ Finset.range N, w N i = 1)
    (hb : ∀ y ∈ Ys, |c z y - c z' y| ≤ e) :
    |weightedCost c w ys N z - weightedCost c w ys N z'| ≤ e := by
  unfold weightedCost weightedMean
  rw [← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range N, (w N i * c z (ys i) - w N i * c z' (ys i))|
      ≤ ∑ i ∈ Finset.range N, |w N i * c z (ys i) - w N i * c z' (ys i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, w N i * e := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [← mul_sub, abs_mul, abs_of_nonneg (hnn i hi')]
        exact mul_le_mul_of_nonneg_left (hb _ (hys i)) (hnn i hi')
    _ = e := by rw [← Finset.sum_mul, hsum, one_mul]

open PrescAnalytics.KNN in
theorem knn_cc_diff {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Ys : Set (EuclideanSpace ℝ (Fin dy))) (x : EuclideanSpace ℝ (Fin dx))
    (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys) (z z' : EuclideanSpace ℝ (Fin dz)) (e : ℝ)
    (hz : Integrable (c z) (μ.condKernel x)) (hz' : Integrable (c z') (μ.condKernel x))
    (hb : ∀ y ∈ Ys, |c z y - c z' y| ≤ e) :
    |condCost μ c z x - condCost μ c z' x| ≤ e := by
  unfold condCost
  rw [← integral_sub hz hz']
  have := norm_integral_le_of_norm_le_const (μ := μ.condKernel x)
    (f := fun y => c z y - c z' y) (C := e)
    (hYx.mono fun y hy => by simpa [Real.norm_eq_abs] using hb y hy)
  simpa [Real.norm_eq_abs] using this

open PrescAnalytics.KNN in
/-- Deterministic step (the proof of Lemma 7 with Assumption 3 available): convergence and
integrability on a countable dense subset `T` of `𝒵` extend to all of `𝒵` by equicontinuity. -/
theorem knn_extend_dense {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z T : Set (EuclideanSpace ℝ (Fin dz))) (hTZ : T ⊆ Z) (hZT : Z ⊆ closure T)
    (Ys : Set (EuclideanSpace ℝ (Fin dy))) (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h4 : Assumption4 c Z Ys)
    (hTint : ∀ t ∈ T, Integrable (c t) (μ.condKernel x))
    (hTconv : ∀ t ∈ T, Tendsto (fun N => weightedCost c w ys N t) atTop (𝓝 (condCost μ c t x))) :
    (∀ z ∈ Z, Integrable (c z) (μ.condKernel x)) ∧
      ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x)) := by
  have happrox : ∀ z ∈ Z, ∀ e > 0, ∃ t ∈ T, ∀ y ∈ Ys, |c z y - c t y| ≤ e := by
    intro z hz e he
    obtain ⟨δ, hδ, hδb⟩ := h4 z hz e he
    obtain ⟨t, htT, hdt⟩ := Metric.mem_closure_iff.mp (hZT hz) δ hδ
    exact ⟨t, htT, hδb t (hTZ htT) (by rw [← dist_eq_norm]; exact le_of_lt hdt)⟩
  have hint : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x) := by
    intro z hz
    choose tseq htT hbd using fun n : ℕ => happrox z hz (1 / ((n : ℝ) + 1)) (by positivity)
    have hmeas : AEStronglyMeasurable (c z) (μ.condKernel x) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hTint _ (htT n)).aestronglyMeasurable) ?_
      filter_upwards [hYx] with y hy
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
      refine ⟨M, fun n hn => ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      calc |c z y - c (tseq n) y| ≤ 1 / ((n : ℝ) + 1) := hbd n y hy
        _ ≤ 1 / ((M : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right hn 1
        _ < ε := hM
    refine ((hTint _ (htT 0)).norm.add (integrable_const (1 : ℝ))).mono' hmeas ?_
    filter_upwards [hYx] with y hy
    have := hbd 0 y hy
    simp only [Nat.cast_zero, zero_add, div_one] at this
    have h1 := abs_sub_abs_le_abs_sub (c z y) (c (tseq 0) y)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  refine ⟨hint, fun z hz => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, htT, hb⟩ := happrox z hz (ε / 4) (by linarith)
  have hT := Metric.tendsto_nhds.mp (hTconv t htT) (ε / 4) (by linarith)
  filter_upwards [hw, hT] with N hN hN2
  have h1 := knn_wc_diff c Ys w ys hys N z t (ε / 4) hN.1 hN.2 hb
  have h2 := knn_cc_diff μ c Ys x hYx z t (ε / 4) (hint z hz) (hTint t htT) hb
  rw [Real.dist_eq] at hN2 ⊢
  have := abs_sub_lt_iff.mp hN2
  have := abs_sub_le_iff.mp h1
  have := abs_sub_le_iff.mp h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

open PrescAnalytics.KNN in
/-- Deterministic core of case 2: eventual coercivity of `Ĉ_N(·|x)` and of `C(·|x)` confines all
minimisers to a ball, where the bounded case of Lemma 6 applies. -/
theorem knn_case2_det {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hZ_closed : IsClosed Z) (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h3x : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x))
    (h4 : Assumption4 c Z Ys)
    (hconv : ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x)))
    (hopt : (optSet μ c Z x).Nonempty)
    (B Rb : ℝ) (hB : ∀ z ∈ Z, Rb ≤ ‖z‖ → ∀ y ∈ Ys, B ≤ c z y)
    (D : Set (EuclideanSpace ℝ (Fin dy))) (hDm : MeasurableSet D)
    (hDpos : 0 < μ.condKernel x D) (hDco : CoerciveUniformlyOn c Z D)
    (hemp : ∀ M : ℝ, ∃ E : Set (EuclideanSpace ℝ (Fin dy)), μ.condKernel x D ≤ μ.condKernel x E ∧
      Tendsto (fun N => weightedMeasure w ys N E) atTop (𝓝 (μ.condKernel x E).toReal) ∧
      ∃ R : ℝ, ∀ z ∈ Z, R ≤ ‖z‖ → ∀ i, ys i ∈ E → M ≤ c z (ys i)) :
    (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (weightedArgmin c w ys Z N).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz), (∀ᶠ N in atTop, zN N ∈ weightedArgmin c w ys Z N) →
        (∀ zstar ∈ optSet μ c Z x,
          Tendsto (fun N => weightedCost c w ys N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
          Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))) ∧
        Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0) := by
  set κx := μ.condKernel x with hκx
  obtain ⟨zs, hzsZ, hzsmin⟩ := hopt
  set v := condCost μ c zs x with hv
  set B' := min B 0 with hB'
  have hB'le : B' ≤ 0 := min_le_right _ _
  have hB'B : B' ≤ B := min_le_left _ _
  set κD := (κx D).toReal with hκD
  have hκDpos : 0 < κD := ENNReal.toReal_pos hDpos.ne' (measure_ne_top _ _)
  set M := 2 * |v + 1 - B'| / κD with hM
  have hM0 : 0 ≤ M := by positivity
  have hMκ : v + 1 - B' ≤ M * κD / 2 := by
    rw [hM]; field_simp; linarith [le_abs_self (v + 1 - B')]
  obtain ⟨R1, hR1⟩ := hDco M
  obtain ⟨E, hκE, hTE, R2, hR2⟩ := hemp M
  have hκEge : κD ≤ (κx E).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hκE
  have hEev : ∀ᶠ N in atTop, κD / 2 < weightedMeasure w ys N E :=
    (tendsto_order.mp hTE).1 _ (by linarith)
  set ρ := max (max R1 R2) (max Rb (‖zs‖ + 1)) with hρ
  have hρR1 : R1 ≤ ρ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hρR2 : R2 ≤ ρ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hρRb : Rb ≤ ρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hρzs : ‖zs‖ + 1 ≤ ρ := le_trans (le_max_right _ _) (le_max_right _ _)
  -- coercivity of the true conditional cost
  have hCco : ∀ z ∈ Z, ρ ≤ ‖z‖ → v + 1 ≤ condCost μ c z x := by
    intro z hz hzρ
    have hpt : ∀ᵐ y ∂κx, D.indicator (fun _ => M) y + B' ≤ c z y := by
      filter_upwards [hYx] with y hy
      by_cases hyD : y ∈ D
      · rw [Set.indicator_of_mem hyD]
        have := hR1 z hz (le_trans hρR1 hzρ) y hyD
        linarith
      · rw [Set.indicator_of_notMem hyD]
        have := hB z hz (le_trans hρRb hzρ) y hy
        linarith
    have hint1 : Integrable (fun y => D.indicator (fun _ => M) y + B') κx :=
      ((integrable_const M).indicator hDm).add (integrable_const B')
    have := integral_mono_ae hint1 (h3x z hz) hpt
    rw [integral_add ((integrable_const M).indicator hDm) (integrable_const B'),
      integral_indicator_const _ hDm, integral_const] at this
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at this
    unfold condCost
    have hmr : κx.real D = κD := rfl
    rw [hmr] at this
    nlinarith
  -- eventual coercivity of the weighted cost
  have hWco : ∀ᶠ N in atTop, ∀ z ∈ Z, ρ ≤ ‖z‖ → v + 1 ≤ weightedCost c w ys N z := by
    filter_upwards [hw, hEev] with N hN hNE
    intro z hz hzρ
    have hterm : ∀ i ∈ Finset.range N,
        w N i * (M * E.indicator 1 (ys i) + B') ≤ w N i * c z (ys i) := by
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hN.1 i (Finset.mem_range.mp hi))
      by_cases hiE : ys i ∈ E
      · rw [Set.indicator_of_mem hiE]
        have := hR2 z hz (le_trans hρR2 hzρ) i hiE
        simp only [Pi.one_apply, mul_one]; linarith
      · rw [Set.indicator_of_notMem hiE]
        have := hB z hz (le_trans hρRb hzρ) (ys i) (hys i)
        simp only [mul_zero, zero_add]; linarith
    have hsum := Finset.sum_le_sum hterm
    have hexp : ∑ i ∈ Finset.range N, w N i * (M * E.indicator 1 (ys i) + B') =
        M * weightedMeasure w ys N E + B' := by
      unfold weightedMeasure weightedMean
      rw [Finset.mul_sum]
      have : ∑ i ∈ Finset.range N, w N i * (M * E.indicator 1 (ys i) + B') =
          ∑ i ∈ Finset.range N, (M * (w N i * E.indicator 1 (ys i)) + B' * w N i) := by
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hN.2, mul_one]
    rw [hexp] at hsum
    unfold weightedCost weightedMean
    nlinarith
  have hzsev : ∀ᶠ N in atTop, weightedCost c w ys N zs < v + 1 :=
    (tendsto_order.mp (hconv zs hzsZ)).2 _ (by linarith)
  -- restrict to a ball
  set Zρ := Z ∩ Metric.closedBall 0 ρ with hZρ
  have hzsρ : zs ∈ Zρ := ⟨hzsZ, by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
  have hZρc : IsClosed Zρ := hZ_closed.inter Metric.isClosed_closedBall
  have hZρb : Bornology.IsBounded Zρ :=
    Metric.isBounded_closedBall.subset Set.inter_subset_right
  have h4ρ : Assumption4 c Zρ Ys := fun z hz ε hε => by
    obtain ⟨δ, hδ, hδb⟩ := h4 z hz.1 ε hε
    exact ⟨δ, hδ, fun z' hz' => hδb z' hz'.1⟩
  have hL := lemma_6_bounded_case μ c Zρ Ys hZρc hZρb ⟨zs, hzsρ⟩ x w ys hys hYx hw
    (fun z hz => h3x z hz.1) h4ρ (fun z hz => hconv z hz.1)
  have hopteq : optSet μ c Zρ x = optSet μ c Z x := by
    ext z
    constructor
    · rintro ⟨hzρ, hzmin⟩
      exact ⟨hzρ.1, fun z' hz' => le_trans (hzmin zs hzsρ) (hzsmin z' hz')⟩
    · rintro ⟨hz, hzmin⟩
      have hzle : condCost μ c z x ≤ v := hzmin zs hzsZ
      have hzn : ‖z‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have := hCco z hz hcon.le
        linarith
      exact ⟨⟨hz, by rw [Metric.mem_closedBall, dist_zero_right]; exact hzn⟩,
        fun z' hz' => hzmin z' hz'.1⟩
  have hargeq : ∀ᶠ N in atTop, weightedArgmin c w ys Z N = weightedArgmin c w ys Zρ N := by
    filter_upwards [hWco, hzsev] with N hN1 hN2
    ext z
    constructor
    · rintro ⟨hz, hzmin⟩
      have hzle := hzmin zs hzsZ
      have hzn : ‖z‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have := hN1 z hz hcon.le
        linarith
      exact ⟨⟨hz, by rw [Metric.mem_closedBall, dist_zero_right]; exact hzn⟩,
        fun z' hz' => hzmin z' hz'.1⟩
    · rintro ⟨hzρ, hzmin⟩
      refine ⟨hzρ.1, fun z' hz' => ?_⟩
      by_cases hz'n : ‖z'‖ ≤ ρ
      · exact hzmin z' ⟨hz', by rw [Metric.mem_closedBall, dist_zero_right]; exact hz'n⟩
      · push_neg at hz'n
        have h1 := hN1 z' hz' hz'n.le
        have h2 := hzmin zs hzsρ
        linarith
  rw [hopteq] at hL
  obtain ⟨hL1, hL2, hL3⟩ := hL
  refine ⟨hL1, ?_, fun zN hzN => hL3 zN ?_⟩
  · filter_upwards [hL2, hargeq] with N h1 h2
    rw [h2]; exact h1
  · filter_upwards [hzN, hargeq] with N h1 h2
    rw [← h2]; exact h1

open PrescAnalytics.KNN in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS_meas : ∀ i, Measurable (S i)) (hS_indep : iIndepFun S P)
    (hS_law : ∀ i, P.map (S i) = μ)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz)))
    (Xs : Set (EuclideanSpace ℝ (Fin dx))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hXs : ∀ᵐ p ∂μ, p.1 ∈ Xs) (hYs : ∀ᵐ p ∂μ, p.2 ∈ Ys)
    (h3 : Assumption3 μ c Z) (h4 : Assumption4 c Z Ys)
    (hZ_closed : IsClosed Z) (hZ_ne : Z.Nonempty)
    (h5_below : CostBoundedBelowAtInfinity c Z Ys)
    (h5_coercive : ∀ x ∈ Xs, ∃ D ⊆ Ys, MeasurableSet D ∧ 0 < μ.condKernel x D ∧
      CoerciveUniformlyOn c Z D)
    (C δ : ℝ) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsAsymptoticallyOptimal P μ c Z (knnArgmin C δ c Z S) ∧
      IsConsistent P μ c Z (knnArgmin C δ c Z S) := by
  set ν := μ.map Prod.fst with hν
  have hdis : ν ⊗ₘ μ.condKernel = μ := Measure.disintegrate μ μ.condKernel
  obtain ⟨T, hTZ, hTc, hZT⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Z).exists_countable_dense_subset
  have hys : ∀ᵐ ω ∂P, ∀ i, (S i ω).2 ∈ Ys := by
    rw [ae_all_iff]; intro i
    have : ∀ᵐ p ∂(P.map (S i)), p.2 ∈ Ys := by rw [hS_law i]; exact hYs
    exact ae_of_ae_map (hS_meas i).aemeasurable this
  have hYx : ∀ᵐ x ∂ν, ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys := by
    have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), p.2 ∈ Ys := by rw [hdis]; exact hYs
    exact Measure.ae_ae_of_ae_compProd this
  have hXsν : ∀ᵐ x ∂ν, x ∈ Xs := by
    have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), p.1 ∈ Xs := by rw [hdis]; exact hXs
    filter_upwards [Measure.ae_ae_of_ae_compProd this] with x hx
    exact hx.exists.choose_spec
  have hTint : ∀ᵐ x ∂ν, ∀ t ∈ T, Integrable (c t) (μ.condKernel x) := by
    rw [ae_ball_iff hTc]
    intro t ht
    have hint : Integrable (fun p => c t p.2) (ν ⊗ₘ μ.condKernel) := by
      rw [hdis]; exact h3.1 t (hTZ ht)
    exact ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  -- measurable versions of `c(t; ·)`, `t ∈ T`
  have hver : ∀ t ∈ T, ∃ h : EuclideanSpace ℝ (Fin dy) → ℝ, Measurable h ∧
      ∀ᵐ p ∂μ, h p.2 = c t p.2 := fun t ht =>
    knn_exists_meas_version μ (c t) (h3.1 t (hTZ ht)).aestronglyMeasurable
  choose! H hHm hHae using hver
  have hdata : ∀ᵐ ω ∂P, ∀ i, ∀ t ∈ T, H t (S i ω).2 = c t (S i ω).2 := by
    rw [ae_all_iff]; intro i
    rw [ae_ball_iff hTc]; intro t ht
    have : ∀ᵐ p ∂(P.map (S i)), H t p.2 = c t p.2 := by rw [hS_law i]; exact hHae t ht
    exact ae_of_ae_map (hS_meas i).aemeasurable this
  have hGx : ∀ᵐ x ∂ν, ∀ᵐ y ∂(μ.condKernel x), ∀ t ∈ T, H t y = c t y := by
    have h1 : ∀ t ∈ T, ∀ᵐ x ∂ν, ∀ᵐ y ∂(μ.condKernel x), H t y = c t y := by
      intro t ht
      have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), H t p.2 = c t p.2 := by rw [hdis]; exact hHae t ht
      exact Measure.ae_ae_of_ae_compProd this
    filter_upwards [(ae_ball_iff hTc).mpr h1] with x hx
    exact (ae_ball_iff hTc).mpr hx
  have hTconv : ∀ t ∈ T, ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
        (fun i => (S i ω).2) N t) atTop (𝓝 (condCost μ c t x)) := by
    intro t ht
    have hint := h3.1 t (hTZ ht)
    have hhint : Integrable (fun p => H t p.2) μ :=
      hint.congr ((hHae t ht).mono fun p hp => hp.symm)
    have hW := walk_knn_strong_consistency μ S hS_meas hS_indep hS_law C δ hC hδ0 hδ1 (H t)
      (hHm t ht) hhint
    have hint_eq : ∀ᵐ x ∂ν, ∫ y, H t y ∂(μ.condKernel x) = condCost μ c t x := by
      have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), H t p.2 = c t p.2 := by rw [hdis]; exact hHae t ht
      filter_upwards [Measure.ae_ae_of_ae_compProd this] with x hx
      exact integral_congr_ae hx
    filter_upwards [hW, hdata] with ω hω hdω
    filter_upwards [hω, hint_eq] with x hx hxe
    rw [← hxe]
    refine hx.congr (fun N => ?_)
    unfold weightedCost weightedMean
    exact Finset.sum_congr rfl (fun i _ => by rw [hdω i t ht])
  have hTconv' : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∀ t ∈ T,
      Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
        (fun i => (S i ω).2) N t) atTop (𝓝 (condCost μ c t x)) := by
    have := (ae_ball_iff hTc).mpr hTconv
    filter_upwards [this] with ω hω
    exact (ae_ball_iff hTc).mpr hω
  -- the countable family of level sets
  let E : ℕ → ℕ → Set (EuclideanSpace ℝ (Fin dy)) := fun M R =>
    ⋂ t ∈ {t ∈ T | (R : ℝ) ≤ ‖t‖}, {y | (M : ℝ) ≤ H t y}
  have hEm : ∀ M R, MeasurableSet (E M R) := fun M R =>
    MeasurableSet.biInter (hTc.mono (Set.sep_subset _ _))
      (fun t ht => measurableSet_le measurable_const (hHm t ht.1))
  have hEconv : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∀ M R : ℕ,
      Tendsto (fun N => weightedMeasure (knnWeight C δ (fun i => (S i ω).1) x)
        (fun i => (S i ω).2) N (E M R)) atTop (𝓝 (μ.condKernel x (E M R)).toReal) := by
    have h1 : ∀ M R : ℕ, ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
        Tendsto (fun N => weightedMeasure (knnWeight C δ (fun i => (S i ω).1) x)
          (fun i => (S i ω).2) N (E M R)) atTop (𝓝 (μ.condKernel x (E M R)).toReal) := by
      intro M R
      have hmeas : Measurable ((E M R).indicator (1 : EuclideanSpace ℝ (Fin dy) → ℝ)) :=
        measurable_const.indicator (hEm M R)
      have hint : Integrable (fun p => (E M R).indicator
          (1 : EuclideanSpace ℝ (Fin dy) → ℝ) p.2) μ := by
        refine (integrable_const (1 : ℝ)).mono' (hmeas.comp measurable_snd).aestronglyMeasurable
          (Eventually.of_forall fun p => ?_)
        by_cases hp : p.2 ∈ E M R
        · simp [Set.indicator_of_mem hp]
        · simp [Set.indicator_of_notMem hp]
      have hW := walk_knn_strong_consistency μ S hS_meas hS_indep hS_law C δ hC hδ0 hδ1 _
        hmeas hint
      filter_upwards [hW] with ω hω
      filter_upwards [hω] with x hx
      rw [integral_indicator_one (hEm M R)] at hx
      exact hx
    have h2 : ∀ᵐ ω ∂P, ∀ M R : ℕ, ∀ᵐ x ∂ν,
        Tendsto (fun N => weightedMeasure (knnWeight C δ (fun i => (S i ω).1) x)
          (fun i => (S i ω).2) N (E M R)) atTop (𝓝 (μ.condKernel x (E M R)).toReal) := by
      rw [ae_all_iff]; intro M; rw [ae_all_iff]; intro R; exact h1 M R
    filter_upwards [h2] with ω hω
    rw [ae_all_iff]; intro M; rw [ae_all_iff]; intro R; exact hω M R
  have key : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (knnArgmin C δ c Z S N ω x).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz), (∀ᶠ N in atTop, zN N ∈ knnArgmin C δ c Z S N ω x) →
        (∀ zstar ∈ optSet μ c Z x,
          Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
            (fun i => (S i ω).2) N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
          Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))) ∧
        Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0) := by
    filter_upwards [hTconv', hys, hdata, hEconv] with ω hωT hωys hωd hωE
    filter_upwards [hωT, hYx, hTint, hGx, hXsν, h3.2, hωE] with x hxT hxY hxI hxG hxX hxopt hxE
    have hw := knn_weights_good C δ hC (fun i => (S i ω).1) x
    obtain ⟨hint_all, hconv_all⟩ := knn_extend_dense μ c Z T hTZ hZT Ys x
      (knnWeight C δ (fun i => (S i ω).1) x) (fun i => (S i ω).2) hωys hxY hw h4 hxI hxT
    obtain ⟨D, _, hDm, hDpos, hDco⟩ := h5_coercive x hxX
    obtain ⟨B, Rb, hB⟩ := h5_below
    refine knn_case2_det μ c Z Ys hZ_closed x (knnWeight C δ (fun i => (S i ω).1) x)
      (fun i => (S i ω).2) hωys hxY hw hint_all h4 hconv_all hxopt B Rb hB D hDm hDpos hDco ?_
    intro M
    set Mn : ℕ := ⌈M⌉₊ + 1 with hMn
    obtain ⟨R0, hR0⟩ := hDco (Mn : ℝ)
    set Rn : ℕ := ⌈R0⌉₊ with hRn
    refine ⟨E Mn Rn, ?_, hxE Mn Rn, (Rn : ℝ) + 1, ?_⟩
    · refine measure_mono_ae ?_
      filter_upwards [hxG] with y hy
      intro hyD
      show y ∈ E Mn Rn
      simp only [E, Set.mem_iInter, Set.mem_setOf_eq]
      intro t ht
      rw [hy t ht.1]
      exact hR0 t (hTZ ht.1) (le_trans (Nat.le_ceil R0) ht.2) y hyD
    · intro z hz hzR i hiE
      obtain ⟨δz, hδz, hδzb⟩ := h4 z hz 1 one_pos
      obtain ⟨t, htT, hdt⟩ := Metric.mem_closure_iff.mp (hZT hz) (min δz 1)
        (lt_min hδz one_pos)
      have hdt' : ‖z - t‖ < min δz 1 := by rw [← dist_eq_norm]; exact hdt
      have hb := hδzb t (hTZ htT) (le_trans hdt'.le (min_le_left _ _)) _ (hωys i)
      have htn : (Rn : ℝ) ≤ ‖t‖ := by
        have h1 : ‖z‖ ≤ ‖t‖ + ‖z - t‖ := by
          have := norm_add_le t (z - t); simp only [add_sub_cancel] at this; linarith
        have h2 := lt_of_lt_of_le hdt' (min_le_right _ _)
        linarith
      have hiE' : (S i ω).2 ∈ E Mn Rn := hiE
      simp only [E, Set.mem_iInter, Set.mem_setOf_eq] at hiE'
      have h1 := hiE' t ⟨htT, htn⟩
      rw [hωd i t htT] at h1
      have h2 : M ≤ ⌈M⌉₊ := Nat.le_ceil M
      have h3' : ((Mn : ℕ) : ℝ) = (⌈M⌉₊ : ℝ) + 1 := by rw [hMn]; push_cast; ring
      rw [h3'] at h1
      have := abs_sub_le_iff.mp hb
      linarith
  constructor
  · filter_upwards [key] with ω hω
    filter_upwards [hω] with x hx
    exact ⟨hx.1, hx.2.1, fun zN hzN zstar hz => ((hx.2.2 zN hzN).1 zstar hz).2⟩
  · filter_upwards [key] with ω hω
    filter_upwards [hω] with x hx
    exact ⟨hx.1, hx.2.1, fun zN hzN => (hx.2.2 zN hzN).2⟩
-- 
