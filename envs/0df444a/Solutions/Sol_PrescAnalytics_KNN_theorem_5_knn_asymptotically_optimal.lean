-- Prove2me | solution 1 for PrescAnalytics.KNN.theorem_5_knn_asymptotically_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:18:06.881281+00:00
-- url     : https://prove2.me/submissions/e1970fcc-11df-491c-b4b3-bdb2083548ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic
import Theorems.Thm_PrescAnalytics_KNN_walk_knn_strong_consistency
import Theorems.Thm_PrescAnalytics_KNN_lemma_6_bounded_case
import Theorems.Thm_PrescAnalytics_KNN_theorem_5_knn_unbounded_case

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
    (h3 : Assumption3 μ c Z) (h4 : Assumption4 c Z Ys) (h5 : Assumption5 μ c Z Xs Ys)
    (C δ : ℝ) (hC : 0 < C) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsAsymptoticallyOptimal P μ c Z (knnArgmin C δ c Z S) ∧
      IsConsistent P μ c Z (knnArgmin C δ c Z S) := by
  obtain ⟨hZc, hZne, hbdd | ⟨h5b, h5D⟩⟩ := h5
  swap
  · exact theorem_5_knn_unbounded_case μ S hS_meas hS_indep hS_law c Z Xs Ys hXs hYs h3 h4
      hZc hZne h5b h5D C δ hC hδ0 hδ1
  set ν := μ.map Prod.fst with hν
  have hdis : ν ⊗ₘ μ.condKernel = μ := Measure.disintegrate μ μ.condKernel
  obtain ⟨T, hTZ, hTc, hZT⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Z).exists_countable_dense_subset
  -- a.s. along the data, the data lie in `𝒴`
  have hys : ∀ᵐ ω ∂P, ∀ i, (S i ω).2 ∈ Ys := by
    rw [ae_all_iff]; intro i
    have : ∀ᵐ p ∂(P.map (S i)), p.2 ∈ Ys := by rw [hS_law i]; exact hYs
    exact ae_of_ae_map (hS_meas i).aemeasurable this
  -- for `μ_X`-a.e. `x`, `μ_{Y|x}(𝒴) = 1`
  have hYx : ∀ᵐ x ∂ν, ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys := by
    have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), p.2 ∈ Ys := by rw [hdis]; exact hYs
    exact Measure.ae_ae_of_ae_compProd this
  -- for `μ_X`-a.e. `x`, `c(t; ·)` is `μ_{Y|x}`-integrable for every `t ∈ T`
  have hTint : ∀ᵐ x ∂ν, ∀ t ∈ T, Integrable (c t) (μ.condKernel x) := by
    rw [ae_ball_iff hTc]
    intro t ht
    have hint : Integrable (fun p => c t p.2) (ν ⊗ₘ μ.condKernel) := by
      rw [hdis]; exact h3.1 t (hTZ ht)
    exact ((Measure.integrable_compProd_iff hint.aestronglyMeasurable).mp hint).1
  -- Walk's theorem at each `t ∈ T`
  have hTconv : ∀ t ∈ T, ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
        (fun i => (S i ω).2) N t) atTop (𝓝 (condCost μ c t x)) := by
    intro t ht
    have hint := h3.1 t (hTZ ht)
    obtain ⟨h, hhm, hhae⟩ := knn_exists_meas_version μ (c t) hint.aestronglyMeasurable
    have hhint : Integrable (fun p => h p.2) μ := hint.congr (hhae.mono fun p hp => hp.symm)
    have hW := walk_knn_strong_consistency μ S hS_meas hS_indep hS_law C δ hC hδ0 hδ1 h hhm hhint
    have hdata : ∀ᵐ ω ∂P, ∀ i, h (S i ω).2 = c t (S i ω).2 := by
      rw [ae_all_iff]; intro i
      have : ∀ᵐ p ∂(P.map (S i)), h p.2 = c t p.2 := by rw [hS_law i]; exact hhae
      exact ae_of_ae_map (hS_meas i).aemeasurable this
    have hint_eq : ∀ᵐ x ∂ν, ∫ y, h y ∂(μ.condKernel x) = condCost μ c t x := by
      have : ∀ᵐ p ∂(ν ⊗ₘ μ.condKernel), h p.2 = c t p.2 := by rw [hdis]; exact hhae
      filter_upwards [Measure.ae_ae_of_ae_compProd this] with x hx
      exact integral_congr_ae hx
    filter_upwards [hW, hdata] with ω hω hdω
    filter_upwards [hω, hint_eq] with x hx hxe
    rw [← hxe]
    refine hx.congr (fun N => ?_)
    unfold weightedCost weightedMean
    exact Finset.sum_congr rfl (fun i _ => by rw [hdω i])
  have hTconv' : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∀ t ∈ T,
      Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
        (fun i => (S i ω).2) N t) atTop (𝓝 (condCost μ c t x)) := by
    have := (ae_ball_iff hTc).mpr hTconv
    filter_upwards [this] with ω hω
    exact (ae_ball_iff hTc).mpr hω
  -- the deterministic conclusion of Lemma 6 holds a.s. for `μ_X`-a.e. `x`
  have key : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (knnArgmin C δ c Z S N ω x).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz), (∀ᶠ N in atTop, zN N ∈ knnArgmin C δ c Z S N ω x) →
        (∀ zstar ∈ optSet μ c Z x,
          Tendsto (fun N => weightedCost c (knnWeight C δ (fun i => (S i ω).1) x)
            (fun i => (S i ω).2) N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
          Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))) ∧
        Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0) := by
    filter_upwards [hTconv', hys] with ω hωT hωys
    filter_upwards [hωT, hYx, hTint] with x hxT hxY hxI
    have hw := knn_weights_good C δ hC (fun i => (S i ω).1) x
    obtain ⟨hint_all, hconv_all⟩ := knn_extend_dense μ c Z T hTZ hZT Ys x
      (knnWeight C δ (fun i => (S i ω).1) x) (fun i => (S i ω).2) hωys hxY hw h4 hxI hxT
    exact lemma_6_bounded_case μ c Z Ys hZc hbdd hZne x
      (knnWeight C δ (fun i => (S i ω).1) x) (fun i => (S i ω).2) hωys hxY hw hint_all h4
      hconv_all
  constructor
  · filter_upwards [key] with ω hω
    filter_upwards [hω] with x hx
    exact ⟨hx.1, hx.2.1, fun zN hzN zstar hz => ((hx.2.2 zN hzN).1 zstar hz).2⟩
  · filter_upwards [key] with ω hω
    filter_upwards [hω] with x hx
    exact ⟨hx.1, hx.2.1, fun zN hzN => (hx.2.2 zN hzN).2⟩
