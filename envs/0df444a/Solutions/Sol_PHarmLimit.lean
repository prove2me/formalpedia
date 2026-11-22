-- Prove2me | solution 1 for PHarmLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:12:34.917857+00:00
-- url     : https://prove2.me/submissions/05d732b3-17f0-41b7-946b-b63f7d07d542

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_PFluxContinuity
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmLimit
import Theorems.Thm_PFluxContinuity
import Theorems.Thm_VanishingOffTsupport


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane) (U : Plane → ℝ) (G : Plane → Plane)
    (hn : ∀ n : ℕ, IsPHarm p Ω (u n) (g n))
    (hU : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn u U Filter.atTop K)
    (hG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → TendstoUniformlyOn g G Filter.atTop K) :
    IsPHarm p Ω U G := by
  have hOopen : IsOpen Ω := (hn 0).openOmega
  have hOmeas : MeasurableSet Ω := hOopen.measurableSet
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  -- Elementary real-power bounds (the paper's clauses (3), (4), (5) on real powers).
  have hpow1 : ∀ t : ℝ, 0 ≤ t → t ^ (p - 1) ≤ 1 + t ^ p := by
    intro t ht
    rcases le_or_gt t 1 with hle | hgt
    · have h1 : t ^ (p - 1) ≤ 1 := Real.rpow_le_one ht hle hp1
      have h2 : (0 : ℝ) ≤ t ^ p := Real.rpow_nonneg ht p
      linarith
    · have h1 : t ^ (p - 1) ≤ t ^ p :=
        Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
      linarith
  have hpow2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 + t ^ p := by
    intro t ht
    rcases le_or_gt t 1 with hle | hgt
    · have h2 : (0 : ℝ) ≤ t ^ p := Real.rpow_nonneg ht p
      linarith
    · have h1 : t ^ (1 : ℝ) ≤ t ^ p := Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
      rw [Real.rpow_one] at h1
      linarith
  have hpow3 : ∀ a : ℝ, 0 ≤ a → (a + 1) ^ p ≤ 2 ^ p * (a ^ p + 1) := by
    intro a ha
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
    have hap : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
    rcases le_or_gt a 1 with hle | hgt
    · have h1 : (a + 1) ^ p ≤ (2 : ℝ) ^ p :=
        Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
      nlinarith
    · have h1 : (a + 1) ^ p ≤ (2 * a) ^ p :=
        Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
      rw [Real.mul_rpow (by norm_num) ha] at h1
      nlinarith
  -- `g n → G` pointwise at every point of `Ω` (singletons are compact subsets).
  have hGpt : ∀ y ∈ Ω, Filter.Tendsto (fun n => g n y) Filter.atTop (nhds (G y)) := by
    intro y hy
    exact (hG {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton).tendsto_at rfl
  have hUpt : ∀ y ∈ Ω, Filter.Tendsto (fun n => u n y) Filter.atTop (nhds (U y)) := by
    intro y hy
    exact (hU {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton).tendsto_at rfl
  -- (2) `U` is continuous on `Ω`:  a uniform limit of continuous functions on a closed ball.
  have hcontU : ContinuousOn U Ω := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hOopen x hx
    have hKsub : Metric.closedBall x (δ / 2) ⊆ Ω := by
      intro y hy
      refine hball ?_
      simp only [Metric.mem_closedBall] at hy
      simp only [Metric.mem_ball]
      linarith
    have hcK : ContinuousOn U (Metric.closedBall x (δ / 2)) :=
      (hU _ hKsub (isCompact_closedBall x (δ / 2))).continuousOn
        ((Filter.Eventually.of_forall fun n => (hn n).contU.mono hKsub).frequently)
    exact (hcK.continuousAt
      (Metric.closedBall_mem_nhds x (by linarith))).continuousWithinAt
  -- (3) `G` is a.e. strongly measurable, being a pointwise limit.
  have hmeasG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Ω) := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => (hn n).measG) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hOmeas] with y hy using hGpt y hy
  -- (4) `|G|^p` is integrable on every compact subset, by a tail comparison with `|g N|^p`.
  have hlocG : ∀ K : Set Plane, K ⊆ Ω → IsCompact K →
      MeasureTheory.IntegrableOn (fun x => ‖G x‖ ^ p) K := by
    intro K hK hKc
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp (hG K hK hKc) 1 one_pos)
    have hbnd : ∀ y ∈ K, ‖G y‖ ≤ ‖g N y‖ + 1 := by
      intro y hy
      have h1 : dist (G y) (g N y) < 1 := hN N le_rfl y hy
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le (G y) (g N y)
      linarith
    have hbdint : MeasureTheory.IntegrableOn
        (fun y : Plane => (2 : ℝ) ^ p * (‖g N y‖ ^ p + 1)) K := by
      have h1 : MeasureTheory.IntegrableOn (fun y : Plane => ‖g N y‖ ^ p + 1) K :=
        ((hn N).locIntG K hK hKc).add
          (MeasureTheory.integrableOn_const hKc.measure_lt_top.ne)
      exact h1.const_mul _
    have hGK : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict K) :=
      hmeasG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hK)
    refine MeasureTheory.Integrable.mono' hbdint
      ((Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable hGK.norm) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKc.measurableSet] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    calc ‖G y‖ ^ p ≤ (‖g N y‖ + 1) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) (hbnd y hy) hp0.le
      _ ≤ 2 ^ p * (‖g N y‖ ^ p + 1) := hpow3 _ (norm_nonneg _)
  -- Vanishing off the topological support, and localization of an `Ω`-integral onto it.
  obtain ⟨hval0, hgrad0⟩ := VanishingOffTsupport
  have hlocR : ∀ K₀ : Set Plane, K₀ ⊆ Ω → ∀ F : Plane → ℝ, (∀ y, y ∉ K₀ → F y = 0) →
      ∫ y in Ω, F y = ∫ y in K₀, F y := fun K₀ hK₀ F hF =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOmeas hK₀
      fun y hy => hF y hy.2
  have hlocP : ∀ K₀ : Set Plane, K₀ ⊆ Ω → ∀ F : Plane → Plane, (∀ y, y ∉ K₀ → F y = 0) →
      ∫ y in Ω, F y = ∫ y in K₀, F y := fun K₀ hK₀ F hF =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOmeas hK₀
      fun y hy => hF y hy.2
  refine ⟨hOopen, hcontU, hmeasG, hlocG, ?_, ?_⟩
  · -- (5) `G` is the distributional gradient of `U`:  two dominated-convergence passages.
    intro φ hφ hφc hφsub
    have hK₀c : IsCompact (tsupport φ) := hφc
    have hK₀meas : MeasurableSet (tsupport φ) := hK₀c.measurableSet
    have hDφcont : Continuous fun y : Plane => gradient φ y :=
      ((InnerProductSpace.toDual ℝ Plane).symm.continuous).comp
        ((hφ.of_le (by simp)).continuous_fderiv one_ne_zero)
    obtain ⟨B, hB⟩ := hK₀c.exists_bound_of_continuousOn hDφcont.continuousOn
    obtain ⟨B', hB'⟩ := hK₀c.exists_bound_of_continuousOn hφ.continuous.continuousOn
    have hl1 : ∀ n : ℕ, ∫ y in Ω, u n y • gradient φ y
        = ∫ y in tsupport φ, u n y • gradient φ y := fun n =>
      hlocP _ hφsub _ fun y hy => by rw [hgrad0 φ y hy, smul_zero]
    have hl2 : ∀ n : ℕ, ∫ y in Ω, φ y • g n y = ∫ y in tsupport φ, φ y • g n y := fun n =>
      hlocP _ hφsub _ fun y hy => by rw [hval0 φ y hy, zero_smul]
    have hl3 : ∫ y in Ω, U y • gradient φ y = ∫ y in tsupport φ, U y • gradient φ y :=
      hlocP _ hφsub _ fun y hy => by rw [hgrad0 φ y hy, smul_zero]
    have hl4 : ∫ y in Ω, φ y • G y = ∫ y in tsupport φ, φ y • G y :=
      hlocP _ hφsub _ fun y hy => by rw [hval0 φ y hy, zero_smul]
    have hid : ∀ n : ℕ, ∫ y in tsupport φ, u n y • gradient φ y
        = - ∫ y in tsupport φ, φ y • g n y := by
      intro n
      rw [← hl1 n, ← hl2 n]
      exact (hn n).weakGrad φ hφ hφc hφsub
    have hlim1 : Filter.Tendsto (fun n => ∫ y in tsupport φ, u n y • gradient φ y)
        Filter.atTop (nhds (∫ y in tsupport φ, U y • gradient φ y)) := by
      obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
        (Metric.tendstoUniformlyOn_iff.mp (hU _ hφsub hK₀c) 1 one_pos)
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun y => (‖U y‖ + 1) * B) (Filter.Eventually.of_forall fun n => ?_) ?_ ?_ ?_
      · exact (((hn n).contU.mono hφsub).aestronglyMeasurable hK₀meas).smul
          hDφcont.aestronglyMeasurable
      · refine Filter.eventually_atTop.mpr ⟨N₁, fun n hnn => ?_⟩
        filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        have h1 : dist (U y) (u n y) < 1 := hN₁ n hnn y hy
        rw [dist_eq_norm] at h1
        have h2 : ‖u n y‖ ≤ ‖U y‖ + 1 := by
          have h3 := norm_sub_norm_le (u n y) (U y)
          rw [norm_sub_rev] at h3
          linarith
        rw [norm_smul]
        exact mul_le_mul h2 (hB y hy) (norm_nonneg _) (by positivity)
      · exact ContinuousOn.integrableOn_compact hK₀c
          (((hcontU.mono hφsub).norm.add continuousOn_const).mul continuousOn_const)
      · filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        exact (hUpt y (hφsub hy)).smul_const _
    have hlim2 : Filter.Tendsto (fun n => ∫ y in tsupport φ, φ y • g n y)
        Filter.atTop (nhds (∫ y in tsupport φ, φ y • G y)) := by
      obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
        (Metric.tendstoUniformlyOn_iff.mp (hG _ hφsub hK₀c) 1 one_pos)
      have hGK : MeasureTheory.AEStronglyMeasurable G
          (MeasureTheory.volume.restrict (tsupport φ)) :=
        hmeasG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hφsub)
      have hGnorm : MeasureTheory.IntegrableOn (fun y : Plane => ‖G y‖) (tsupport φ) := by
        have h1 : MeasureTheory.IntegrableOn (fun y : Plane => 1 + ‖G y‖ ^ p) (tsupport φ) :=
          (MeasureTheory.integrableOn_const hK₀c.measure_lt_top.ne).add (hlocG _ hφsub hK₀c)
        refine MeasureTheory.Integrable.mono' h1 hGK.norm ?_
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hpow2 _ (norm_nonneg _)
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun y => B' * (‖G y‖ + 1)) (Filter.Eventually.of_forall fun n => ?_) ?_ ?_ ?_
      · exact hφ.continuous.aestronglyMeasurable.smul
          ((hn n).measG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hφsub))
      · refine Filter.eventually_atTop.mpr ⟨N₂, fun n hnn => ?_⟩
        filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        have h1 : dist (G y) (g n y) < 1 := hN₂ n hnn y hy
        rw [dist_eq_norm] at h1
        have h2 : ‖g n y‖ ≤ ‖G y‖ + 1 := by
          have h3 := norm_sub_norm_le (g n y) (G y)
          rw [norm_sub_rev] at h3
          linarith
        rw [norm_smul]
        exact mul_le_mul (hB' y hy) h2 (norm_nonneg _) (le_trans (norm_nonneg _) (hB' y hy))
      · have h4 : MeasureTheory.IntegrableOn (fun y : Plane => ‖G y‖ + 1) (tsupport φ) :=
          hGnorm.add (MeasureTheory.integrableOn_const hK₀c.measure_lt_top.ne)
        exact h4.const_mul _
      · filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        exact (hGpt y (hφsub hy)).const_smul _
    rw [hl3, hl4]
    refine tendsto_nhds_unique hlim1 ?_
    simp only [hid]
    exact hlim2.neg
  · -- (6) the weak equation:  dominated convergence THROUGH the flux, which is where
    -- continuity of `A_p` at the origin is indispensable.
    intro φ hφ hφc hφsub
    have hK₀c : IsCompact (tsupport φ) := hφc
    have hK₀meas : MeasurableSet (tsupport φ) := hK₀c.measurableSet
    have hDφcont : Continuous fun y : Plane => gradient φ y :=
      ((InnerProductSpace.toDual ℝ Plane).symm.continuous).comp
        ((hφ.of_le (by simp)).continuous_fderiv one_ne_zero)
    obtain ⟨B, hB⟩ := hK₀c.exists_bound_of_continuousOn hDφcont.continuousOn
    have hfluxnorm : ∀ ξ : Plane, ‖PFlux p ξ‖ = ‖ξ‖ ^ (p - 1) := (PFluxContinuity p hp hp2).1
    have hfluxcont : Continuous (PFlux p) := (PFluxContinuity p hp hp2).2
    have hl5 : ∀ n : ℕ, ∫ y in Ω, (inner ℝ (PFlux p (g n y)) (gradient φ y) : ℝ)
        = ∫ y in tsupport φ, (inner ℝ (PFlux p (g n y)) (gradient φ y) : ℝ) := fun n =>
      hlocR _ hφsub _ fun y hy => by rw [hgrad0 φ y hy, inner_zero_right]
    have hl6 : ∫ y in Ω, (inner ℝ (PFlux p (G y)) (gradient φ y) : ℝ)
        = ∫ y in tsupport φ, (inner ℝ (PFlux p (G y)) (gradient φ y) : ℝ) :=
      hlocR _ hφsub _ fun y hy => by rw [hgrad0 φ y hy, inner_zero_right]
    have hid : ∀ n : ℕ,
        ∫ y in tsupport φ, (inner ℝ (PFlux p (g n y)) (gradient φ y) : ℝ) = 0 := by
      intro n
      rw [← hl5 n]
      exact (hn n).eqn φ hφ hφc hφsub
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp (hG _ hφsub hK₀c) 1 one_pos)
    have hbdint : MeasureTheory.IntegrableOn
        (fun y : Plane => B * (1 + 2 ^ p * (‖G y‖ ^ p + 1))) (tsupport φ) := by
      have h1 : MeasureTheory.IntegrableOn (fun y : Plane => ‖G y‖ ^ p + 1) (tsupport φ) :=
        (hlocG _ hφsub hK₀c).add (MeasureTheory.integrableOn_const hK₀c.measure_lt_top.ne)
      have h2 : MeasureTheory.IntegrableOn
          (fun y : Plane => 1 + 2 ^ p * (‖G y‖ ^ p + 1)) (tsupport φ) :=
        (MeasureTheory.integrableOn_const hK₀c.measure_lt_top.ne).add (h1.const_mul _)
      exact h2.const_mul _
    have hlim : Filter.Tendsto
        (fun n => ∫ y in tsupport φ, (inner ℝ (PFlux p (g n y)) (gradient φ y) : ℝ))
        Filter.atTop
        (nhds (∫ y in tsupport φ, (inner ℝ (PFlux p (G y)) (gradient φ y) : ℝ))) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun y => B * (1 + 2 ^ p * (‖G y‖ ^ p + 1)))
        (Filter.Eventually.of_forall fun n => ?_) ?_ hbdint ?_
      · have hgn : MeasureTheory.AEStronglyMeasurable (g n)
            (MeasureTheory.volume.restrict (tsupport φ)) :=
          (hn n).measG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hφsub)
        have hfl : MeasureTheory.AEStronglyMeasurable (fun y => PFlux p (g n y))
            (MeasureTheory.volume.restrict (tsupport φ)) :=
          hfluxcont.comp_aestronglyMeasurable hgn
        exact continuous_inner.comp_aestronglyMeasurable
          (hfl.prodMk hDφcont.aestronglyMeasurable)
      · refine Filter.eventually_atTop.mpr ⟨N, fun n hnn => ?_⟩
        filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        have h1 : dist (G y) (g n y) < 1 := hN n hnn y hy
        rw [dist_eq_norm] at h1
        have h2 : ‖g n y‖ ≤ ‖G y‖ + 1 := by
          have h3 := norm_sub_norm_le (g n y) (G y)
          rw [norm_sub_rev] at h3
          linarith
        have h4 : ‖PFlux p (g n y)‖ ≤ 1 + 2 ^ p * (‖G y‖ ^ p + 1) := by
          rw [hfluxnorm]
          calc ‖g n y‖ ^ (p - 1) ≤ 1 + ‖g n y‖ ^ p := hpow1 _ (norm_nonneg _)
            _ ≤ 1 + (‖G y‖ + 1) ^ p := by
                  have h5 := Real.rpow_le_rpow (norm_nonneg (g n y)) h2 hp0.le
                  linarith
            _ ≤ 1 + 2 ^ p * (‖G y‖ ^ p + 1) := by
                  have h6 := hpow3 _ (norm_nonneg (G y))
                  linarith
        rw [Real.norm_eq_abs]
        calc |(inner ℝ (PFlux p (g n y)) (gradient φ y) : ℝ)|
            ≤ ‖PFlux p (g n y)‖ * ‖gradient φ y‖ := abs_real_inner_le_norm _ _
          _ ≤ (1 + 2 ^ p * (‖G y‖ ^ p + 1)) * B :=
              mul_le_mul h4 (hB y hy) (norm_nonneg _) (by positivity)
          _ = B * (1 + 2 ^ p * (‖G y‖ ^ p + 1)) := by ring
      · filter_upwards [MeasureTheory.ae_restrict_mem hK₀meas] with y hy
        have h1 : Filter.Tendsto (fun n => PFlux p (g n y)) Filter.atTop
            (nhds (PFlux p (G y))) := (hfluxcont.tendsto (G y)).comp (hGpt y (hφsub hy))
        exact Filter.Tendsto.inner h1 tendsto_const_nhds
    rw [hl6]
    refine tendsto_nhds_unique hlim ?_
    simp only [hid]
    exact tendsto_const_nhds
