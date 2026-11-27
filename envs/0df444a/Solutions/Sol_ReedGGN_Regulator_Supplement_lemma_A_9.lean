-- Prove2me | solution 1 for ReedGGN.Regulator.Supplement.lemma_A_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:44:12.603329+00:00
-- url     : https://prove2.me/submissions/ab022611-cefb-4115-9593-d454df336802

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

open ReedGGN
open ReedGGN.Regulator
open ReedGGN.Regulator.Supplement

theorem solution (μ : Measure ℝ) (hμ : ServiceLaw μ) :
    (∀ x : State 3, Admissible x → Admissible (convolutionMap μ x)) ∧
    Measurable (fun x : {x : State 3 // Admissible x} => convolutionMap μ x.val) ∧
    ∀ (x : State 3), (∀ i, Continuous (x.2 i)) →
      ∀ xs : ℕ → State 3, ProductJ1 xs x →
        ProductJ1 (fun n => convolutionMap μ (xs n)) (convolutionMap μ x) := by
          have : IsProbabilityMeasure μ := hμ.1
          -- local boundedness of cadlag paths
          have L0 : ∀ y : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag y →
              ∀ T : ℝ≥0, ∃ C, ∀ u ≤ T, |y u| ≤ C := by
            intro y hy T
            have hc : IsCompact (Set.Icc (0:ℝ≥0) T) := isCompact_Icc
            have key : BddAbove ((fun v => |y v|) '' Set.Icc (0:ℝ≥0) T) := by
              refine hc.induction_on (p := fun S => BddAbove ((fun v => |y v|) '' S)) ?_ ?_ ?_ ?_
              · simp
              · intro s t hst ht
                exact ht.mono (Set.image_mono hst)
              · intro s t hs ht
                rw [Set.image_union]; exact hs.union ht
              · intro u _
                have hloc : ∃ C, ∀ᶠ v in 𝓝 u, |y v| ≤ C := by
                  have h1 : ∀ᶠ v in 𝓝[≥] u, |y v| ≤ |y u| + 1 := by
                    have := (hy.1 u).tendsto
                    have h2 : ∀ᶠ v in 𝓝[≥] u, dist (y v) (y u) < 1 :=
                      this (Metric.ball_mem_nhds _ one_pos)
                    filter_upwards [h2] with v hv
                    rw [Real.dist_eq] at hv
                    have := abs_sub_abs_le_abs_sub (y v) (y u)
                    linarith
                  rcases eq_or_ne u 0 with hu | hu
                  · refine ⟨|y u| + 1, ?_⟩
                    rw [← nhdsLT_sup_nhdsGE]
                    refine Filter.eventually_sup.2 ⟨?_, h1⟩
                    subst hu
                    have : (𝓝[<] (0:ℝ≥0)) = ⊥ := by
                      rw [show Set.Iio (0:ℝ≥0) = ∅ by ext v; simp]
                      exact nhdsWithin_empty _
                    rw [this]; exact Filter.eventually_bot
                  · obtain ⟨a, ha⟩ := hy.2 u (pos_iff_ne_zero.2 hu)
                    have h3 : ∀ᶠ v in 𝓝[<] u, dist (y v) a < 1 := ha (Metric.ball_mem_nhds _ one_pos)
                    refine ⟨max (|y u| + 1) (|a| + 1), ?_⟩
                    rw [← nhdsLT_sup_nhdsGE]
                    refine Filter.eventually_sup.2 ⟨?_, ?_⟩
                    · filter_upwards [h3] with v hv
                      rw [Real.dist_eq] at hv
                      have := abs_sub_abs_le_abs_sub (y v) a
                      have := le_max_right (|y u| + 1) (|a| + 1)
                      linarith
                    · filter_upwards [h1] with v hv
                      exact hv.trans (le_max_left _ _)
                obtain ⟨C, hC⟩ := hloc
                refine ⟨{v | |y v| ≤ C}, mem_nhdsWithin_of_mem_nhds hC, C, ?_⟩
                rintro _ ⟨v, hv, rfl⟩; exact hv
            obtain ⟨C, hC⟩ := key
            exact ⟨C, fun u hu => hC ⟨u, ⟨bot_le, hu⟩, rfl⟩⟩
          -- joint measurability via dyadic right approximations
          have L1 : ∀ (X : Type) [MeasurableSpace X] (Y : X → ℝ≥0 → ℝ) (U : X → ℝ≥0),
              (∀ u, Measurable fun x => Y x u) → Measurable U →
              (∀ x t, ContinuousWithinAt (Y x) (Set.Ici t) t) → Measurable fun x => Y x (U x) := by
            intro X _ Y U hY hU hc
            let c : ℕ → ℝ≥0 → ℝ≥0 := fun n u => (⌈u * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
            have hcl : ∀ u, Tendsto (fun n => c n u) atTop (𝓝[≥] u) := by
              intro u
              rw [tendsto_nhdsWithin_iff]
              have hlo : ∀ n, u ≤ c n u := by
                intro n
                show u ≤ _
                rw [le_div_iff₀ (by positivity)]; exact Nat.le_ceil _
              refine ⟨?_, Eventually.of_forall hlo⟩
              have hhi : ∀ n, c n u ≤ u + (1 / 2) ^ n := by
                intro n
                show _ / _ ≤ _
                rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_pow,
                  inv_mul_cancel₀ (by positivity)]
                exact (Nat.ceil_lt_add_one (by positivity)).le
              have ht : Tendsto (fun n : ℕ => u + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 u) := by
                have := (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num))
                simpa using tendsto_const_nhds.add this
              exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hlo hhi
            refine measurable_of_tendsto_metrizable (f := fun n x => Y x (c n (U x))) ?_ ?_
            · intro n
              have : Measurable fun p : X × ℕ => Y p.1 ((p.2 : ℝ≥0) / 2 ^ n) :=
                measurable_from_prod_countable_left (fun k => hY ((k : ℝ≥0) / 2 ^ n))
              exact this.comp (measurable_id.prodMk ((Nat.measurable_ceil.comp (hU.mul_const _))))
            · rw [tendsto_pi_nhds]; intro x
              exact (hc x (U x)).tendsto.comp (hcl (U x))
          have Lm : ∀ y : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag y → Measurable y := by
            intro y hy
            exact L1 ℝ≥0 (fun _ => y) id (fun _ => measurable_const) measurable_id (fun _ t => hy.1 t)
          have tail_eq : ∀ t, tail μ t = 1 - cdf μ t := by
            intro t
            rw [cdf_eq_real, tail, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
              ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, measureReal_def]
          have tail_nn : ∀ t, 0 ≤ tail μ t := fun t => ENNReal.toReal_nonneg
          have tail_le : ∀ t, tail μ t ≤ 1 := by
            intro t; rw [tail_eq]; have := cdf_nonneg μ t; linarith
          have L2 : KurtzProtter91.Integrals.IsCadlag (fun t : ℝ≥0 => tail μ t) := by
            constructor
            · intro t
              have hr : ContinuousWithinAt (fun s : ℝ => tail μ s) (Set.Ici (t:ℝ)) t := by
                have : (fun s : ℝ => tail μ s) = fun s => 1 - cdf μ s := funext tail_eq
                rw [this]
                exact continuousWithinAt_const.sub ((cdf μ).right_continuous t)
              exact hr.comp NNReal.continuous_coe.continuousWithinAt (fun s hs => NNReal.coe_le_coe.2 hs)
            · intro t _
              have hanti : Antitone (fun t : ℝ≥0 => tail μ t) := fun a b hab => by
                simp only [tail_eq]; have := (cdf μ).mono (NNReal.coe_le_coe.2 hab); linarith
              exact ⟨_, hanti.tendsto_nhdsLT t⟩
          have L3 : ∀ y : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag y →
              KurtzProtter91.Integrals.IsCadlag
                (fun t : ℝ≥0 => ∫ s in Set.Ioc (0 : ℝ) t, y (Real.toNNReal ((t : ℝ) - s)) ∂μ) := by
            intro y hy
            choose! L hL using hy.2
            have ym := Lm y hy
            let F : ℝ≥0 → ℝ → ℝ := fun t =>
              Set.indicator (Set.Ioc 0 (t:ℝ)) (fun s => y (Real.toNNReal ((t:ℝ) - s)))
            have hFeq : (fun t : ℝ≥0 => ∫ s in Set.Ioc (0 : ℝ) t, y (Real.toNNReal ((t : ℝ) - s)) ∂μ)
                = fun t => ∫ s, F t s ∂μ := by
              funext t; exact (integral_indicator measurableSet_Ioc).symm
            rw [hFeq]
            have hFm : ∀ t, AEStronglyMeasurable (F t) μ := by
              intro t
              exact ((ym.comp (measurable_const.sub measurable_id).real_toNNReal).indicator
                measurableSet_Ioc).aestronglyMeasurable
            have hFb : ∀ t0 : ℝ≥0, ∃ C, ∀ t ≤ t0 + 1, ∀ s, ‖F t s‖ ≤ C := by
              intro t0
              obtain ⟨C, hC⟩ := L0 y hy (t0 + 1)
              refine ⟨C, fun t ht s => ?_⟩
              have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 bot_le)
              simp only [F, Set.indicator]
              split_ifs with hs
              · rw [Real.norm_eq_abs]
                apply hC
                refine le_trans ?_ ht
                rw [Real.toNNReal_le_iff_le_coe]; linarith [hs.1]
              · simpa using hC0
            have hev : ∀ t0 : ℝ≥0, ∀ᶠ t : ℝ≥0 in 𝓝 t0, t ≤ t0 + 1 :=
              fun t0 => (eventually_lt_nhds (lt_add_one t0)).mono fun t ht => le_of_lt ht
            have hcts : ∀ s : ℝ, Continuous fun t : ℝ≥0 => Real.toNNReal ((t:ℝ) - s) :=
              fun s => continuous_real_toNNReal.comp (NNReal.continuous_coe.sub continuous_const)
            constructor
            · intro t0
              obtain ⟨C, hC⟩ := hFb t0
              refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
                (Eventually.of_forall hFm) ?_ (integrable_const C) (Eventually.of_forall fun s => ?_)
              · filter_upwards [nhdsWithin_le_nhds (hev t0)] with t ht
                exact Eventually.of_forall (hC t ht)
              · rcases le_or_gt s 0 with hs | hs
                · have : ∀ t, F t s = 0 := fun t => by
                    simp only [F]; rw [Set.indicator_of_notMem]; simp only [Set.mem_Ioc, not_and]
                    intro h; linarith
                  simp only [this]; exact tendsto_const_nhds
                rcases le_or_gt s (t0:ℝ) with hs2 | hs2
                · have e1 : ∀ᶠ t : ℝ≥0 in 𝓝[≥] t0, y (Real.toNNReal ((t:ℝ) - s)) = F t s := by
                    filter_upwards [self_mem_nhdsWithin] with t ht
                    have : (t0:ℝ) ≤ t := NNReal.coe_le_coe.2 ht
                    simp only [F]; rw [Set.indicator_of_mem]; exact ⟨hs, by linarith⟩
                  have e0 : F t0 s = y (Real.toNNReal ((t0:ℝ) - s)) := by
                    simp only [F]; rw [Set.indicator_of_mem]; exact ⟨hs, hs2⟩
                  rw [e0]
                  refine Tendsto.congr' e1 ?_
                  refine (hy.1 _).tendsto.comp ?_
                  rw [tendsto_nhdsWithin_iff]
                  refine ⟨((hcts s).tendsto t0).mono_left nhdsWithin_le_nhds, ?_⟩
                  filter_upwards [self_mem_nhdsWithin] with t ht
                  have : (t0:ℝ) ≤ t := NNReal.coe_le_coe.2 ht
                  exact Real.toNNReal_le_toNNReal (by linarith)
                · have e1 : ∀ᶠ t : ℝ≥0 in 𝓝[≥] t0, (0:ℝ) = F t s := by
                    have : ∀ᶠ t : ℝ≥0 in 𝓝 t0, (t:ℝ) < s :=
                      (NNReal.continuous_coe.tendsto t0).eventually (Iio_mem_nhds hs2)
                    filter_upwards [nhdsWithin_le_nhds this] with t ht
                    simp only [F]; rw [Set.indicator_of_notMem]; simp only [Set.mem_Ioc, not_and]
                    intro _ h; linarith
                  have e0 : F t0 s = 0 := by
                    simp only [F]; rw [Set.indicator_of_notMem]; simp only [Set.mem_Ioc, not_and]
                    intro _ h; linarith
                  rw [e0]
                  exact Tendsto.congr' e1 tendsto_const_nhds
            · intro t0 ht0
              obtain ⟨C, hC⟩ := hFb t0
              let f : ℝ → ℝ := fun s => if s ∈ Set.Ioo 0 (t0:ℝ) then L (Real.toNNReal ((t0:ℝ) - s)) else 0
              refine ⟨∫ s, f s ∂μ, tendsto_integral_filter_of_dominated_convergence (fun _ => C)
                (Eventually.of_forall hFm) ?_ (integrable_const C) (Eventually.of_forall fun s => ?_)⟩
              · filter_upwards [nhdsWithin_le_nhds (hev t0)] with t ht
                exact Eventually.of_forall (hC t ht)
              · rcases le_or_gt s 0 with hs | hs
                · have : ∀ t, F t s = 0 := fun t => by
                    simp only [F]; rw [Set.indicator_of_notMem]; simp only [Set.mem_Ioc, not_and]
                    intro h; linarith
                  have hf : f s = 0 := by
                    simp only [f, Set.mem_Ioo]; rw [if_neg]; intro h; linarith [h.1]
                  simp only [this, hf]; exact tendsto_const_nhds
                rcases lt_or_ge s (t0:ℝ) with hs2 | hs2
                · have e1 : ∀ᶠ t : ℝ≥0 in 𝓝[<] t0, y (Real.toNNReal ((t:ℝ) - s)) = F t s := by
                    have : ∀ᶠ t : ℝ≥0 in 𝓝 t0, s < (t:ℝ) :=
                      (NNReal.continuous_coe.tendsto t0).eventually (Ioi_mem_nhds hs2)
                    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with t ht ht'
                    have : (t:ℝ) < t0 := NNReal.coe_lt_coe.2 ht
                    simp only [F]; rw [Set.indicator_of_mem]; exact ⟨hs, by linarith⟩
                  have e0 : f s = L (Real.toNNReal ((t0:ℝ) - s)) := by
                    simp only [f]; rw [if_pos]; exact ⟨hs, hs2⟩
                  rw [e0]
                  refine Tendsto.congr' e1 ?_
                  refine (hL _ (Real.toNNReal_pos.2 (by linarith))).comp ?_
                  rw [tendsto_nhdsWithin_iff]
                  refine ⟨((hcts s).tendsto t0).mono_left nhdsWithin_le_nhds, ?_⟩
                  filter_upwards [self_mem_nhdsWithin] with t ht
                  have : (t:ℝ) < t0 := NNReal.coe_lt_coe.2 ht
                  exact (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 (by linarith)
                · have e1 : ∀ᶠ t : ℝ≥0 in 𝓝[<] t0, (0:ℝ) = F t s := by
                    filter_upwards [self_mem_nhdsWithin] with t ht
                    have : (t:ℝ) < t0 := NNReal.coe_lt_coe.2 ht
                    simp only [F]; rw [Set.indicator_of_notMem]; simp only [Set.mem_Ioc, not_and]
                    intro _ h; linarith
                  have e0 : f s = 0 := by
                    simp only [f, Set.mem_Ioo]; rw [if_neg]; intro h; linarith [h.2]
                  rw [e0]
                  exact Tendsto.congr' e1 tendsto_const_nhds
          have Csub : ∀ a b : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag a →
              KurtzProtter91.Integrals.IsCadlag b →
              KurtzProtter91.Integrals.IsCadlag (fun t => a t - b t) := by
            intro a b ha hb
            refine ⟨fun t => (ha.1 t).sub (hb.1 t), fun t ht => ?_⟩
            obtain ⟨a1, h1⟩ := ha.2 t ht
            obtain ⟨b1, h2⟩ := hb.2 t ht
            exact ⟨_, h1.sub h2⟩
          have Cmul : ∀ a b : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag a →
              KurtzProtter91.Integrals.IsCadlag b →
              KurtzProtter91.Integrals.IsCadlag (fun t => a t * b t) := by
            intro a b ha hb
            refine ⟨fun t => (ha.1 t).mul (hb.1 t), fun t ht => ?_⟩
            obtain ⟨a1, h1⟩ := ha.2 t ht
            obtain ⟨b1, h2⟩ := hb.2 t ht
            exact ⟨_, h1.mul h2⟩
          have Cconst : ∀ c : ℝ, KurtzProtter91.Integrals.IsCadlag (fun _ : ℝ≥0 => c) :=
            fun c => ⟨fun t => continuousWithinAt_const, fun t _ => ⟨c, tendsto_const_nhds⟩⟩
          have L4 : ∀ y : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag y →
              KurtzProtter91.Integrals.IsCadlag (incrementTransform μ y) := by
            intro y hy
            exact Csub _ _ (Csub _ _ (Cmul _ _ (Cconst _) hy) (L3 y hy)) (Cmul _ _ L2 (Cconst _))
          have hint : ∀ y : ℝ≥0 → ℝ, KurtzProtter91.Integrals.IsCadlag y → ∀ t : ℝ≥0,
              IntegrableOn (fun s => y (Real.toNNReal ((t:ℝ) - s))) (Set.Ioc 0 (t:ℝ)) μ := by
            intro y hy t
            obtain ⟨C, hC⟩ := L0 y hy t
            refine Integrable.of_bound
              ((Lm y hy).comp (measurable_const.sub measurable_id).real_toNNReal).aestronglyMeasurable C
              (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
            rw [Real.norm_eq_abs]
            apply hC
            rw [Real.toNNReal_le_iff_le_coe]; linarith [hs.1]
          have L5 : ∀ (ys : ℕ → RPath) (y : RPath), Continuous y →
              KurtzProtter91.Integrals.SkorohodTendsto ys y →
              KurtzProtter91.Integrals.TendstoUniformlyOnBounded ys y := by
            intro ys y hyc hS T
            obtain ⟨_, _, l, hl, h1, h2⟩ := hS
            rw [Metric.tendstoUniformlyOn_iff]
            intro ε hε
            have hK : IsCompact (Set.Icc (0:ℝ≥0) (T + 1)) := isCompact_Icc
            obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
              (hK.uniformContinuousOn_of_continuous hyc.continuousOn) (ε / 2) (by positivity)
            have e1 := Metric.tendstoUniformlyOn_iff.1 (h1 (T + 1)) (ε / 2) (by positivity)
            have e2 := Metric.tendstoUniformlyOn_iff.1 (h2 (T + 1)) (min δ 1) (by positivity)
            filter_upwards [e1, e2] with n hn1 hn2
            intro t ht
            obtain ⟨u, hu⟩ := (hl n).2.2 t
            have hT1 : T + 1 ∈ Set.Icc (0:ℝ≥0) (T + 1) := ⟨bot_le, le_rfl⟩
            have hlT : T < l n (T + 1) := by
              have h3 := hn2 (T + 1) hT1
              rw [NNReal.dist_eq] at h3
              have hm := min_le_right δ 1
              have h4 := (abs_lt.1 (lt_of_lt_of_le h3 hm)).2
              have : (T:ℝ) < l n (T + 1) := by simp at h4; linarith
              exact_mod_cast this
            have hu_le : u ≤ T + 1 := by
              by_contra h
              rw [not_le] at h
              have h5 := (hl n).2.1 h
              rw [hu] at h5
              exact absurd (lt_of_lt_of_le (hlT.trans h5) ht.2) (lt_irrefl _)
            have hu_mem : u ∈ Set.Icc (0:ℝ≥0) (T + 1) := ⟨bot_le, hu_le⟩
            have a1 := hn1 u hu_mem
            have a2 : dist (y t) (y u) < ε / 2 := by
              refine hδu t ⟨bot_le, ht.2.trans (by simp)⟩ u hu_mem ?_
              rw [← hu, dist_comm]
              exact lt_of_lt_of_le (hn2 u hu_mem) (min_le_left _ _)
            calc dist (y t) (ys n t) ≤ dist (y t) (y u) + dist (y u) (ys n t) := dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add a2 (by rw [← hu]; simpa using a1)
              _ = ε := add_halves ε
          have L6 : ∀ (ys : ℕ → RPath) (y : RPath), Continuous y →
              KurtzProtter91.Integrals.SkorohodTendsto ys y →
              KurtzProtter91.Integrals.SkorohodTendsto (fun n => incrementTransform μ (ys n))
                (incrementTransform μ y) := by
            intro ys y hc hS
            refine ⟨fun n => L4 _ (hS.1 n), L4 _ hS.2.1, fun _ => id,
              fun _ => ⟨continuous_id, strictMono_id, Function.surjective_id⟩, ?_, ?_⟩
            · intro T
              have hu := L5 ys y hc hS T
              rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
              intro ε hε
              filter_upwards [hu (ε / 4) (by positivity)] with n hn
              intro t ht
              have bnd : ∀ u ≤ T, |y u - ys n u| < ε / 4 := by
                intro u hu'
                have := hn u ⟨bot_le, hu'⟩
                rwa [Real.dist_eq] at this
              show dist (incrementTransform μ y t) (incrementTransform μ (ys n) t) < ε
              have hdiff : (∫ s in Set.Ioc (0:ℝ) t, y (Real.toNNReal ((t:ℝ) - s)) ∂μ) -
                  ∫ s in Set.Ioc (0:ℝ) t, ys n (Real.toNNReal ((t:ℝ) - s)) ∂μ =
                  ∫ s in Set.Ioc (0:ℝ) t, (y (Real.toNNReal ((t:ℝ) - s)) -
                    ys n (Real.toNNReal ((t:ℝ) - s))) ∂μ :=
                (integral_sub (hint y hS.2.1 t) (hint (ys n) (hS.1 n) t)).symm
              have hI : |∫ s in Set.Ioc (0:ℝ) t, (y (Real.toNNReal ((t:ℝ) - s)) -
                    ys n (Real.toNNReal ((t:ℝ) - s))) ∂μ| ≤ ε / 4 := by
                have h6 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := Set.Ioc (0:ℝ) t)
                  (C := ε / 4) (measure_lt_top _ _)
                  (f := fun s => y (Real.toNNReal ((t:ℝ) - s)) - ys n (Real.toNNReal ((t:ℝ) - s)))
                  (fun s hs => by
                    rw [Real.norm_eq_abs]
                    refine (bnd _ (le_trans ?_ ht.2)).le
                    rw [Real.toNNReal_le_iff_le_coe]; linarith [hs.1])
                rw [Real.norm_eq_abs] at h6
                refine h6.trans ?_
                have h7 : μ.real (Set.Ioc (0:ℝ) t) ≤ 1 := measureReal_le_one
                have h8 : 0 ≤ μ.real (Set.Ioc (0:ℝ) t) := measureReal_nonneg
                nlinarith
              have hA : |tail μ 0 * (y t - ys n t)| ≤ ε / 4 := by
                rw [abs_mul, abs_of_nonneg (tail_nn 0)]
                exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (tail_le 0)) (bnd t ht.2).le
              have hB : |tail μ t * (y 0 - ys n 0)| ≤ ε / 4 := by
                rw [abs_mul, abs_of_nonneg (tail_nn _)]
                exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (tail_le _)) (bnd 0 bot_le).le
              rw [Real.dist_eq]
              simp only [incrementTransform, arrivalTransform]
              have key : tail μ 0 * y t - (∫ s in Set.Ioc (0:ℝ) t, y (Real.toNNReal ((t:ℝ) - s)) ∂μ) -
                  tail μ t * y 0 - (tail μ 0 * ys n t -
                    (∫ s in Set.Ioc (0:ℝ) t, ys n (Real.toNNReal ((t:ℝ) - s)) ∂μ) - tail μ t * ys n 0)
                  = tail μ 0 * (y t - ys n t) - ((∫ s in Set.Ioc (0:ℝ) t, y (Real.toNNReal ((t:ℝ) - s)) ∂μ) -
                  ∫ s in Set.Ioc (0:ℝ) t, ys n (Real.toNNReal ((t:ℝ) - s)) ∂μ) -
                    tail μ t * (y 0 - ys n 0) := by ring
              rw [key, hdiff]
              have := abs_le.1 hA
              have := abs_le.1 hB
              have := abs_le.1 hI
              rw [abs_lt]; constructor <;> linarith
            · intro T
              rw [Metric.tendstoUniformlyOn_iff]
              intro ε hε
              exact Eventually.of_forall fun n x _ => by simpa using hε
          refine ⟨?_, ?_, ?_⟩
          · intro x hx i
            fin_cases i
            · exact hx 0
            · exact L4 _ (hx 1)
            · exact hx 2
          · have hsub : Measurable (fun x : {x : State 3 // Admissible x} => x.val) :=
              measurable_subtype_coe
            have hcoord : ∀ i : Fin 3, Measurable (fun x : {x : State 3 // Admissible x} => x.val.2 i) :=
              fun i => (measurable_pi_apply i).comp (measurable_snd.comp hsub)
            have hev : ∀ u : ℝ≥0, Measurable (fun x : {x : State 3 // Admissible x} => x.val.2 1 u) :=
              fun u => (measurable_pi_apply u).comp (hcoord 1)
            have hT : Measurable (fun x : {x : State 3 // Admissible x} =>
                incrementTransform μ (x.val.2 1)) := by
              rw [measurable_pi_iff]
              intro t
              let g : {x : State 3 // Admissible x} × ℝ → ℝ := fun p =>
                p.1.val.2 1 (Real.toNNReal ((t:ℝ) - p.2))
              have hg : Measurable g :=
                L1 ({x : State 3 // Admissible x} × ℝ) (fun p => p.1.val.2 1) (fun p => Real.toNNReal ((t:ℝ) - p.2))
                  (fun u => (hev u).comp measurable_fst)
                  (measurable_const.sub measurable_snd).real_toNNReal
                  (fun p u => (p.1.property 1).1 u)
              let f : {x : State 3 // Admissible x} × ℝ → ℝ :=
                Set.indicator {p | p.2 ∈ Set.Ioc (0:ℝ) t} g
              have hf : Measurable f := hg.indicator (measurable_snd measurableSet_Ioc)
              have hI : Measurable (fun x : {x : State 3 // Admissible x} =>
                  ∫ s in Set.Ioc (0 : ℝ) t, x.val.2 1 (Real.toNNReal ((t : ℝ) - s)) ∂μ) := by
                have heq : (fun x : {x : State 3 // Admissible x} =>
                    ∫ s in Set.Ioc (0 : ℝ) t, x.val.2 1 (Real.toNNReal ((t : ℝ) - s)) ∂μ) =
                    fun x => ∫ s, f (x, s) ∂μ := by
                  funext x
                  rw [← integral_indicator measurableSet_Ioc]
                  congr 1
                rw [heq]
                exact (hf.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
              exact (((measurable_const.mul (hev t)).sub hI).sub (measurable_const.mul (hev 0)))
            refine Measurable.prodMk (measurable_fst.comp hsub) ?_
            rw [measurable_pi_iff]
            intro i
            fin_cases i
            · exact hcoord 0
            · exact hT
            · exact hcoord 2
          · intro x hxc xs hxs
            refine ⟨hxs.1, fun i => ?_⟩
            fin_cases i
            · exact hxs.2 0
            · exact L6 _ _ (hxc 1) (hxs.2 1)
            · exact hxs.2 2
