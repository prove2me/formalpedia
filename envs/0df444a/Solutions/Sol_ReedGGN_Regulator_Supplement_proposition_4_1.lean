-- Prove2me | solution 1 for ReedGGN.Regulator.Supplement.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:41.623796+00:00
-- url     : https://prove2.me/submissions/7bc60702-8208-4c54-a5cc-c79184247302

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

open ReedGGN
open ReedGGN.Regulator
open ReedGGN.Regulator.Supplement

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀) :
    WeakJ1 P P (fun n ω => one (wbar q n ω)) (fun _ => one (fun _ => 0)) := by
      haveI : IsProbabilityMeasure μ₀ := q.residual_law.1
      set F : ℝ → ℝ := fun t => (μ₀ (Set.Ioi t)).toReal with hF
      set r : ℕ → Ω → ℝ := q.residual with hr
      set K : ℕ → Ω → ℕ := fun n ω => min (q.sample n ω 0).Q₀ (n + 1) with hK
      have hw : ∀ n ω (t : ℝ≥0), wbar q n ω t = (∑ i ∈ Finset.Icc 1 (K n ω),
          ((if (t : ℝ) < r i ω then (1 : ℝ) else 0) - F t)) / ((n + 1 : ℕ) : ℝ) := by
        intro n ω t
        simp only [wbar, localSample, ReedGGN.SystemEq.W0, ReedGGN.SystemEq.F0bar, q.initial_agrees,
          q.size, q.residual_eq, hF, hr, hK]
      -- SLLN for indicators
      have hslln : ∀ S : Set ℝ, MeasurableSet S → ∀ᵐ ω ∂P, Tendsto (fun k : ℕ =>
          (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, S.indicator (fun _ => (1 : ℝ)) (r (i + 1) ω)) atTop
          (𝓝 (μ₀ S).toReal) := by
        intro S hS
        have hg : Measurable (S.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hS
        have h := strong_law_ae (μ := P)
          (fun i ω => S.indicator (fun _ => (1 : ℝ)) (r (i + 1) ω)) ?_ ?_ ?_
        · have hE : (∫ ω, S.indicator (fun _ => (1 : ℝ)) (r (0 + 1) ω) ∂P) = (μ₀ S).toReal := by
            have := q.residual_dist 0
            rw [← integral_map (q.residual_measurable _).aemeasurable hg.aestronglyMeasurable]
            rw [this, integral_indicator hS]
            simp [Measure.real]
          rw [hE] at h
          filter_upwards [h] with ω hω
          simpa [smul_eq_mul] using hω
        · refine Integrable.of_bound (C := 1) ?_ ?_
          · exact (hg.comp (q.residual_measurable _)).aestronglyMeasurable
          · refine Eventually.of_forall (fun ω => ?_)
            by_cases h : r (0+1) ω ∈ S <;> simp [Set.indicator, h]
        · intro i j hij
          exact (q.residual_iid.comp (fun _ => S.indicator (fun _ => (1 : ℝ)))
            (fun _ => hg)).indepFun hij
        · intro i
          have h1 : IdentDistrib (r (i+1)) (r (0+1)) P P :=
            ⟨(q.residual_measurable _).aemeasurable, (q.residual_measurable _).aemeasurable,
              by rw [q.residual_dist i, q.residual_dist 0]⟩
          exact h1.comp hg
      have hsmall : ∀ δ : ℝ, 0 < δ → ∀ A : ℕ → Set ℝ, Antitone A → (∀ j, MeasurableSet (A j)) →
          (⋂ j, A j) = ∅ → ∃ j, (μ₀ (A j)).toReal ≤ δ := by
        intro δ hδ A hA hAm hAe
        have h := tendsto_measure_iInter_atTop (μ := μ₀) (fun j => (hAm j).nullMeasurableSet) hA
          ⟨0, measure_ne_top _ _⟩
        rw [hAe, measure_empty] at h
        have : ∀ᶠ j in atTop, (μ₀ ∘ A) j < ENNReal.ofReal δ :=
          h.eventually (gt_mem_nhds (by simpa using hδ))
        obtain ⟨j, hj⟩ := this.exists
        exact ⟨j, ENNReal.toReal_le_of_le_ofReal hδ.le hj.le⟩
      have hgrid : ∀ δ : ℝ, 0 < δ → ∃ s : Finset ℝ, ∀ t : ℝ, 0 ≤ t →
          (∃ a ∈ s, a ≤ t ∧ F a ≤ δ) ∨
          (∃ a ∈ s, ∃ b ∈ s, a ≤ t ∧ t < b ∧ (μ₀ (Set.Ioo a b)).toReal ≤ δ) := by
        intro δ hδ
        obtain ⟨T, hT⟩ := hsmall δ hδ (fun j => Set.Ioi (j : ℝ))
          (fun i j hij => Set.Ioi_subset_Ioi (by exact_mod_cast hij)) (fun _ => measurableSet_Ioi)
          (by
            ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
            obtain ⟨j, hj⟩ := exists_nat_ge x
            exact ⟨j, hj⟩)
        have hd1 : ∀ t : ℝ, ∃ j : ℕ, (μ₀ (Set.Ioc t (t + 1 / ((j : ℝ) + 1)))).toReal ≤ δ := by
          intro t
          refine hsmall δ hδ _ ?_ (fun _ => measurableSet_Ioc) ?_
          · intro i j hij
            apply Set.Ioc_subset_Ioc le_rfl
            gcongr
          · ext x; simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_forall]
            by_contra h
            push Not at h
            obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 (h 0).1)
            have := (h j).2
            linarith
        have hd2 : ∀ t : ℝ, ∃ j : ℕ, (μ₀ (Set.Ioo (t - 1 / ((j : ℝ) + 1)) t)).toReal ≤ δ := by
          intro t
          refine hsmall δ hδ _ ?_ (fun _ => measurableSet_Ioo) ?_
          · intro i j hij
            apply Set.Ioo_subset_Ioo _ le_rfl
            gcongr
          · ext x; simp only [Set.mem_iInter, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_forall]
            by_contra h
            push Not at h
            obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 (h 0).2)
            have := (h j).1
            linarith
        choose j1 hj1 using hd1
        choose j2 hj2 using hd2
        set d1 : ℝ → ℝ := fun t => 1 / ((j1 t : ℝ) + 1)
        set d2 : ℝ → ℝ := fun t => 1 / ((j2 t : ℝ) + 1)
        have hd1p : ∀ t, 0 < d1 t := fun t => by positivity
        have hd2p : ∀ t, 0 < d2 t := fun t => by positivity
        obtain ⟨c, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).elim_finite_subcover
          (fun t => Set.Ioo (t - d2 t) (t + d1 t)) (fun _ => isOpen_Ioo)
          (fun t _ => Set.mem_iUnion.2 ⟨t, by
            constructor <;> linarith [hd1p t, hd2p t]⟩)
        refine ⟨insert (T : ℝ) (c ∪ c.image (fun t => t - d2 t) ∪ c.image (fun t => t + d1 t)), ?_⟩
        intro t ht
        by_cases hTt : (T : ℝ) ≤ t
        · exact Or.inl ⟨T, by simp, hTt, hT⟩
        · push Not at hTt
          have := hc ⟨ht, hTt.le⟩
          simp only [Set.mem_iUnion, Set.mem_Ioo] at this
          obtain ⟨u, hu, h1, h2⟩ := this
          right
          by_cases htu : t < u
          · refine ⟨u - d2 u, by simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]; exact Or.inr (Or.inl (Or.inr ⟨u, hu, rfl⟩)), u, by simp [hu], h1.le, htu, hj2 u⟩
          · push Not at htu
            refine ⟨u, by simp [hu], u + d1 u, by simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]; exact Or.inr (Or.inr ⟨u, hu, rfl⟩), htu, h2, ?_⟩
            refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
              (measure_mono Set.Ioo_subset_Ioc_self)) (hj1 u)
      have hFanti : ∀ a t : ℝ, a ≤ t → F t ≤ F a := fun a t h =>
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi h))
      have hFIci : ∀ t b : ℝ, t < b → (μ₀ (Set.Ici b)).toReal ≤ F t := fun t b h =>
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ici_subset_Ioi.2 h))
      have hFsplit : ∀ a b : ℝ, a < b → F a = (μ₀ (Set.Ioo a b)).toReal + (μ₀ (Set.Ici b)).toReal := by
        intro a b hab
        simp only [hF]
        rw [← Set.Ioo_union_Ici_eq_Ioi hab, measure_union _ measurableSet_Ici,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact Set.disjoint_left.2 (fun x hx hx' => absurd hx'.out (not_le.2 hx.2))
      set sg : ℕ → Finset ℝ := fun m => Classical.choose (hgrid (1 / ((m : ℝ) + 1)) (by positivity))
        with hsg
      have hsg_spec : ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
          (∃ a ∈ sg m, a ≤ t ∧ F a ≤ 1 / ((m : ℝ) + 1)) ∨
          (∃ a ∈ sg m, ∃ b ∈ sg m, a ≤ t ∧ t < b ∧ (μ₀ (Set.Ioo a b)).toReal ≤ 1 / ((m : ℝ) + 1)) :=
        fun m => Classical.choose_spec (hgrid (1 / ((m : ℝ) + 1)) (by positivity))
      have hgood : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ a ∈ sg m,
          Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
            (if a < r (i + 1) ω then (1 : ℝ) else 0)) atTop (𝓝 (F a)) ∧
          Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
            (if a ≤ r (i + 1) ω then (1 : ℝ) else 0)) atTop (𝓝 (μ₀ (Set.Ici a)).toReal) := by
        rw [ae_all_iff]
        intro m
        rw [eventually_all_finset]
        intro a _
        filter_upwards [hslln _ (measurableSet_Ioi (a := a)), hslln _ (measurableSet_Ici (a := a))]
          with ω h1 h2
        simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Ici] at h1 h2
        exact ⟨h1, h2⟩
      have hGC : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ t : ℝ, 0 ≤ t →
          |∑ i ∈ Finset.range k, ((if t < r (i + 1) ω then (1 : ℝ) else 0) - F t)| ≤ ε * k := by
        filter_upwards [hgood] with ω hω
        intro ε hε
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
        set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
        have hδp : 0 < δ := by positivity
        have hev : ∀ᶠ k : ℕ in atTop, ∀ a ∈ sg m,
            |(k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (if a < r (i + 1) ω then (1 : ℝ) else 0) - F a| < δ ∧
            |(k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (if a ≤ r (i + 1) ω then (1 : ℝ) else 0) -
              (μ₀ (Set.Ici a)).toReal| < δ := by
          rw [eventually_all_finset]
          intro a ha
          have h1 := (hω m a ha).1
          have h2 := (hω m a ha).2
          have e1 := (Metric.tendsto_nhds.1 h1) δ hδp
          have e2 := (Metric.tendsto_nhds.1 h2) δ hδp
          filter_upwards [e1, e2] with k hk1 hk2
          exact ⟨by simpa [Real.dist_eq] using hk1, by simpa [Real.dist_eq] using hk2⟩
        obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
        refine ⟨k0, fun k hk t ht => ?_⟩
        have hkk := hk0 k hk
        set cG : ℝ → ℝ := fun a => ∑ i ∈ Finset.range k, (if a < r (i + 1) ω then (1 : ℝ) else 0)
          with hcG
        set cH : ℝ → ℝ := fun a => ∑ i ∈ Finset.range k, (if a ≤ r (i + 1) ω then (1 : ℝ) else 0)
          with hcH
        have hsum : ∑ i ∈ Finset.range k, ((if t < r (i + 1) ω then (1 : ℝ) else 0) - F t) =
            (k : ℝ) * ((k : ℝ)⁻¹ * cG t - F t) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · subst h0; simp [hcG]
          · have : (k : ℝ) ≠ 0 := by positivity
            field_simp
            rfl
        have hkpos : (0 : ℝ) ≤ k := by positivity
        have hkinv : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
        have hmonoG : ∀ a, a ≤ t → (k : ℝ)⁻¹ * cG t ≤ (k : ℝ)⁻¹ * cG a := by
          intro a hat
          apply mul_le_mul_of_nonneg_left _ hkinv
          apply Finset.sum_le_sum
          intro i _
          split_ifs with h1 h2 <;> (try norm_num) <;> exact absurd (lt_of_le_of_lt hat h1) h2
        have hmonoH : ∀ b, t < b → (k : ℝ)⁻¹ * cH b ≤ (k : ℝ)⁻¹ * cG t := by
          intro b htb
          apply mul_le_mul_of_nonneg_left _ hkinv
          apply Finset.sum_le_sum
          intro i _
          split_ifs with h1 h2 <;> (try norm_num) <;> exact absurd (lt_of_lt_of_le htb h1) h2
        have hG0 : 0 ≤ (k : ℝ)⁻¹ * cG t := by
          apply mul_nonneg hkinv
          apply Finset.sum_nonneg
          intro i _
          split_ifs <;> norm_num
        have hFt0 : 0 ≤ F t := ENNReal.toReal_nonneg
        have hmain : |(k : ℝ)⁻¹ * cG t - F t| ≤ 2 * δ := by
          rcases hsg_spec m t ht with ⟨a, ha, hat, hFa⟩ | ⟨a, ha, b, hb, hat, htb, hab⟩
          · have h1 := (hkk a ha).1
            have h2 := hmonoG a hat
            have h3 := hFanti a t hat
            rw [abs_lt] at h1
            rw [abs_le]
            constructor <;> linarith
          · have h1 := (hkk a ha).1
            have h1' := (hkk b hb).2
            have h2 := hmonoG a hat
            have h2' := hmonoH b htb
            have h3 := hFanti a t hat
            have h4 := hFIci t b htb
            have h5 := hFsplit a b (lt_of_le_of_lt hat htb)
            rw [abs_lt] at h1 h1'
            rw [abs_le]
            constructor <;> linarith
        rw [hsum, abs_mul, abs_of_nonneg hkpos]
        calc (k : ℝ) * |(k : ℝ)⁻¹ * cG t - F t| ≤ k * (2 * δ) :=
              mul_le_mul_of_nonneg_left hmain hkpos
          _ ≤ k * ε := mul_le_mul_of_nonneg_left (by linarith) hkpos
          _ = ε * k := by ring
      have hIcc : ∀ (k : ℕ) (f : ℕ → ℝ), ∑ i ∈ Finset.Icc 1 k, f i = ∑ i ∈ Finset.range k, f (i + 1) := by
        intro k f
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      have hF1 : ∀ t, F t ≤ 1 := fun t =>
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      have hF0 : ∀ t, 0 ≤ F t := fun t => ENNReal.toReal_nonneg
      -- cadlag
      have hFeq : ∀ x : ℝ, F x = 1 - cdf μ₀ x := by
        intro x
        rw [cdf_eq_real]
        simp only [hF, Measure.real]
        rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
          ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      have hFrc : ∀ t : ℝ≥0, ContinuousWithinAt (fun x : ℝ≥0 => F x) (Set.Ici t) t := by
        intro t
        have h1 : ContinuousWithinAt (fun x : ℝ => F x) (Set.Ici (t : ℝ)) t := by
          have : (fun x : ℝ => F x) = fun x => 1 - cdf μ₀ x := funext hFeq
          rw [this]
          exact continuousWithinAt_const.sub ((cdf μ₀).right_continuous _)
        exact h1.comp NNReal.continuous_coe.continuousWithinAt
          (fun x hx => NNReal.coe_le_coe.2 hx)
      have hFa : Antitone (fun x : ℝ≥0 => F x) := fun a b h => hFanti a b (NNReal.coe_le_coe.2 h)
      have hIa : ∀ c : ℝ, Antitone (fun x : ℝ≥0 => if (x : ℝ) < c then (1 : ℝ) else 0) := by
        intro c a b h
        simp only
        split_ifs with h1 h2 <;> norm_num
        exact absurd (lt_of_le_of_lt (NNReal.coe_le_coe.2 h) h1) h2
      have hIrc : ∀ c : ℝ, ∀ t : ℝ≥0, ContinuousWithinAt
          (fun x : ℝ≥0 => if (x : ℝ) < c then (1 : ℝ) else 0) (Set.Ici t) t := by
        intro c t
        by_cases htc : (t : ℝ) < c
        · apply ContinuousAt.continuousWithinAt
          have hev : ∀ᶠ x : ℝ≥0 in 𝓝 t, (x : ℝ) < c :=
            (NNReal.continuous_coe.tendsto t).eventually (gt_mem_nhds htc)
          refine (continuousAt_const (y := (1 : ℝ))).congr ?_
          filter_upwards [hev] with x hx
          simp [hx]
        · refine (continuousWithinAt_const (b := (0 : ℝ))).congr ?_ ?_
          · intro x hx
            have : ¬ (x : ℝ) < c := fun h => htc (lt_of_le_of_lt (NNReal.coe_le_coe.2 hx) h)
            simp [this]
          · simp [htc]
      have hcadW : ∀ n ω, KurtzProtter91.Integrals.IsCadlag (wbar q n ω) := by
        intro n ω
        have heq : wbar q n ω = fun t : ℝ≥0 => ((∑ i ∈ Finset.Icc 1 (K n ω),
            (if (t : ℝ) < r i ω then (1 : ℝ) else 0)) - (K n ω : ℝ) * F t) / ((n + 1 : ℕ) : ℝ) := by
          funext t
          rw [hw, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
        rw [heq]
        have hA : Antitone (fun t : ℝ≥0 => ∑ i ∈ Finset.Icc 1 (K n ω),
            (if (t : ℝ) < r i ω then (1 : ℝ) else 0)) := by
          intro a b h
          exact Finset.sum_le_sum (fun i _ => hIa (r i ω) h)
        constructor
        · intro t
          refine ContinuousWithinAt.div_const (ContinuousWithinAt.sub ?_ ?_) _
          · exact tendsto_finset_sum _ (fun i _ => hIrc (r i ω) t)
          · exact continuousWithinAt_const.mul (hFrc t)
        · intro t _
          exact ⟨_, ((hA.tendsto_nhdsLT t).sub ((hFa.tendsto_nhdsLT t).const_mul _)).div_const _⟩
      have hcad0 : KurtzProtter91.Integrals.IsCadlag (fun _ : ℝ≥0 => (0 : ℝ)) :=
        ⟨fun _ => continuousWithinAt_const, fun _ _ => ⟨0, tendsto_const_nhds⟩⟩
      -- measurability
      have hKm : ∀ n, Measurable (K n) := fun n =>
        (measurable_from_nat (f := fun m : ℕ => min m (n + 1))).comp (q.count_measurable n)
      have hwm : ∀ n (t : ℝ≥0), Measurable (fun ω => wbar q n ω t) := by
        intro n t
        set g : Ω × ℕ → ℝ := fun p => (∑ i ∈ Finset.Icc 1 p.2,
            ((if (t : ℝ) < r i p.1 then (1 : ℝ) else 0) - F t)) / ((n + 1 : ℕ) : ℝ) with hg
        have h : Measurable g := by
          apply measurable_from_prod_countable_left
          intro k
          show Measurable (fun x : Ω => (∑ i ∈ Finset.Icc 1 k,
            ((if (t : ℝ) < r i x then (1 : ℝ) else 0) - F t)) / ((n + 1 : ℕ) : ℝ))
          refine Measurable.div_const (Finset.measurable_sum _ (fun i _ => ?_)) _
          exact (Measurable.ite (measurableSet_lt measurable_const (q.residual_measurable i))
            measurable_const measurable_const).sub measurable_const
        have h2 : (fun ω => wbar q n ω t) = g ∘ (fun ω => (ω, K n ω)) := by
          funext ω
          simp only [Function.comp, hg]
          exact hw n ω t
        rw [h2]
        exact h.comp (measurable_id.prodMk (hKm n))
      have hXm : ∀ n, Measurable (fun ω => one (wbar q n ω)) := by
        intro n
        exact measurable_const.prodMk
          (measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun t => hwm n t)))
      -- uniform bound
      have hbound : ∀ ω, (∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ t : ℝ, 0 ≤ t →
          |∑ i ∈ Finset.range k, ((if t < r (i + 1) ω then (1 : ℝ) else 0) - F t)| ≤ ε * k) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, |wbar q n ω t| ≤ ε := by
        intro ω hω ε hε
        obtain ⟨k0, hk0⟩ := hω ε hε
        obtain ⟨N, hN⟩ := exists_nat_ge ((k0 : ℝ) / ε)
        refine eventually_atTop.2 ⟨N, fun n hn t => ?_⟩
        have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hk0n : (k0 : ℝ) ≤ ε * ((n + 1 : ℕ) : ℝ) := by
          have : (k0 : ℝ) / ε ≤ ((n + 1 : ℕ) : ℝ) := by
            refine le_trans hN ?_
            push_cast
            have : (N : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          rwa [div_le_iff₀ hε, mul_comm] at this
        have hKle : (K n ω : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast (min_le_right _ _)
        rw [hw, hIcc, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
        by_cases hK0 : k0 ≤ K n ω
        · refine le_trans (hk0 _ hK0 t t.2) ?_
          exact mul_le_mul_of_nonneg_left hKle hε.le
        · push Not at hK0
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) (fun i _ => ?_)) ?_
          · have := hF1 t
            have := hF0 t
            rw [abs_le]
            split_ifs <;> constructor <;> linarith
          · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
            have : (K n ω : ℝ) ≤ k0 := by exact_mod_cast hK0.le
            linarith
      refine ⟨fun n => Eventually.of_forall (fun ω i => hcadW n ω),
        Eventually.of_forall (fun ω i => hcad0), Ω, inferInstance, P,
        fun n ω => one (wbar q n ω), fun _ => one (fun _ => 0), inferInstance,
        fun n => IdentDistrib.refl (hXm n).aemeasurable,
        IdentDistrib.refl aemeasurable_const, ?_⟩
      filter_upwards [hGC] with ω hω
      refine ⟨tendsto_const_nhds, fun i => ?_⟩
      show KurtzProtter91.Integrals.SkorohodTendsto (fun n => wbar q n ω) (fun _ => (0 : ℝ))
      refine ⟨fun n => hcadW n ω, hcad0, fun _ => id,
        fun _ => ⟨continuous_id, strictMono_id, Function.surjective_id⟩, ?_, ?_⟩
      · intro T
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        filter_upwards [hbound ω hω (ε / 2) (half_pos hε)] with n hn
        intro t _
        have := hn t
        simp only [Function.comp, id, dist_zero_left, Real.norm_eq_abs]
        linarith
      · intro T
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        exact Eventually.of_forall (fun n t _ => by simpa using hε)
