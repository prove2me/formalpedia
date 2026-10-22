-- Prove2me | solution 1 for SchalAvg.AvgOpt.lemma_2_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:00:16.053124+00:00
-- url     : https://prove2.me/submissions/26cedb53-a0c1-4b64-a30a-8124a989d44e

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE
open SchalAvg.AvgOpt
theorem g69h2_lsc_real {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_meas : Measurable f) (f_nn : 0 ≤ f)
    (f_open : ∀ t : ℝ, IsOpen {a | t < f a})
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) f_meas.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) :=
        lintegral_mono (fun t ↦ h_opens _ (f_open t))
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) :=
        lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

theorem g69h2_iSup_min (a : ℝ≥0∞) : ⨆ K : ℕ, min a (K : ℝ≥0∞) = a := by
  apply le_antisymm (iSup_le fun K => min_le_left _ _)
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp only [top_le_iff, min_eq_right le_top] -- ⨆ K, ↑K = ⊤
    exact ENNReal.iSup_natCast
  · obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le K (le_min le_rfl hK.le)

theorem g69h2_lsc_ennreal {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μ : Measure Ω} {μs : ℕ → Measure Ω} {g : Ω → ℝ≥0∞} (hg : LowerSemicontinuous g)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, g x ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, g x ∂(μs i)) := by
  have gm : Measurable g := hg.measurable
  have hK : ∀ K : ℕ, ∫⁻ x, min (g x) K ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, g x ∂(μs i)) := by
    intro K
    have hof : ∀ x, ENNReal.ofReal (min (g x) K).toReal = min (g x) K := fun x =>
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (min_le_right _ _))
    have key := g69h2_lsc_real (μ := μ) (μs := μs) (f := fun x => (min (g x) K).toReal)
      ((gm.min measurable_const).ennreal_toReal) (fun x => ENNReal.toReal_nonneg) ?_ h_opens
    · simp only [hof] at key
      refine key.trans (liminf_le_liminf (Eventually.of_forall fun i => ?_))
      exact lintegral_mono fun x => min_le_left _ _
    · intro t
      rcases lt_or_ge t 0 with ht | ht
      · have : {a | t < (min (g a) K).toReal} = Set.univ :=
          Set.eq_univ_of_forall fun a => lt_of_lt_of_le ht ENNReal.toReal_nonneg
        rw [this]; exact isOpen_univ
      · have : {a | t < (min (g a) K).toReal} =
            {a | ENNReal.ofReal t < g a} ∩ {a | ENNReal.ofReal t < (K : ℝ≥0∞)} := by
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
          rw [← ENNReal.ofReal_lt_iff_lt_toReal ht
            (ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (min_le_right _ _)), lt_min_iff]
        rw [this]
        exact (hg.isOpen_preimage _).inter isOpen_const
  calc ∫⁻ x, g x ∂μ = ∫⁻ x, ⨆ K : ℕ, min (g x) K ∂μ := by simp only [g69h2_iSup_min]
    _ = ⨆ K : ℕ, ∫⁻ x, min (g x) K ∂μ := by
        apply lintegral_iSup (fun K => gm.min measurable_const)
        intro a b hab x
        exact min_le_min le_rfl (by exact_mod_cast hab)
    _ ≤ _ := iSup_le hK

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure X) (μs : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (w : ℕ → X → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    ∫⁻ x, liminf (fun p : ℕ × X => w p.1 p.2) (atTop ×ˢ 𝓝 x) ∂(μ : Measure X) ≤
      liminf (fun n => ∫⁻ x, w n x ∂(μs n : Measure X)) atTop := by
  set b : ℕ → X → ℝ≥0∞ := fun k x => ⨅ n ≥ k, ⨅ y ∈ Metric.ball x (1 / ((k:ℝ) + 1)), w n y
    with hb_def
  set c : ℕ → X → ℝ≥0∞ := fun k x => ⨆ (t : ℝ≥0∞) (_ : x ∈ interior {z | t < b k z}), t
    with hc_def
  set d : ℕ → X → ℝ≥0∞ := fun k x => ⨆ (j : ℕ) (_ : j ≤ k), c j x with hd_def
  have hc_lsc : ∀ k, LowerSemicontinuous (c k) := by
    intro k x s hs
    simp only [hc_def, lt_iSup_iff] at hs
    obtain ⟨t, hx, hst⟩ := hs
    filter_upwards [isOpen_interior.mem_nhds hx] with x' hx'
    exact lt_of_lt_of_le hst (le_iSup₂ (f := fun (t : ℝ≥0∞) (_ : x' ∈ interior {z | t < b k z}) => t) t hx')
  have hd_lsc : ∀ k, LowerSemicontinuous (d k) := by
    intro k
    exact lowerSemicontinuous_iSup fun j => lowerSemicontinuous_iSup fun _ => hc_lsc j
  have hcb : ∀ k x, c k x ≤ b k x := by
    intro k x
    refine iSup₂_le fun t ht => ?_
    have : x ∈ {z | t < b k z} := interior_subset ht
    exact this.le
  have hbw : ∀ k n, k ≤ n → ∀ x, b k x ≤ w n x := by
    intro k n hkn x
    refine (iInf₂_le n hkn).trans ?_
    exact iInf₂_le x (Metric.mem_ball_self (by positivity))
  have hdw : ∀ k n, k ≤ n → ∀ x, d k x ≤ w n x := by
    intro k n hkn x
    exact iSup₂_le fun j hj => (hcb j x).trans (hbw j n (hj.trans hkn) x)
  have hd_mono : Monotone d := by
    intro k k' hkk' x
    exact iSup₂_le fun j hj => le_iSup₂ (f := fun (j : ℕ) (_ : j ≤ k') => c j x) j (hj.trans hkk')
  have hlow : ∀ x, liminf (fun p : ℕ × X => w p.1 p.2) (atTop ×ˢ 𝓝 x) ≤ ⨆ k, d k x := by
    intro x
    refine le_of_forall_lt fun s hs => ?_
    obtain ⟨s', hss', hs'⟩ := exists_between hs
    obtain ⟨s'', hs's'', hs''⟩ := exists_between hs'
    have hev := eventually_lt_of_lt_liminf hs''
    obtain ⟨t1, ht1, t2, ht2, hsub⟩ := mem_prod_iff.mp hev
    obtain ⟨K, hK⟩ := mem_atTop_sets.mp ht1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht2
    obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (half_pos hε)
    set k := max k0 K
    have hr : 1 / ((k:ℝ) + 1) < ε / 2 := by
      refine lt_of_le_of_lt ?_ hk0
      apply one_div_le_one_div_of_le (by positivity)
      have : (k0:ℝ) ≤ k := by exact_mod_cast le_max_left k0 K
      linarith
    have hbk : ∀ z ∈ Metric.ball x (1 / ((k:ℝ) + 1)), s' < b k z := by
      intro z hz
      refine lt_of_lt_of_le hs's'' ?_
      refine le_iInf₂ fun n hn => le_iInf₂ fun y hy => ?_
      have hyx : y ∈ t2 := by
        apply hball
        rw [Metric.mem_ball] at hy hz ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ < ε := by linarith
      have : (n, y) ∈ t1 ×ˢ t2 := ⟨hK n (le_trans (le_max_right _ _) hn), hyx⟩
      exact (hsub this).le
    have hxint : x ∈ interior {z | s' < b k z} :=
      interior_mono hbk (by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (by positivity))
    have hck : s' ≤ c k x :=
      le_iSup₂ (f := fun (t : ℝ≥0∞) (_ : x ∈ interior {z | t < b k z}) => t) s' hxint
    calc s < s' := hss'
      _ ≤ c k x := hck
      _ ≤ d k x := le_iSup₂ (f := fun (j : ℕ) (_ : j ≤ k) => c j x) k le_rfl
      _ ≤ ⨆ k, d k x := le_iSup (fun k => d k x) k
  have h_opens : ∀ G, IsOpen G →
      (μ : Measure X) G ≤ atTop.liminf (fun i ↦ (μs i : Measure X) G) :=
    fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG
  calc ∫⁻ x, liminf (fun p : ℕ × X => w p.1 p.2) (atTop ×ˢ 𝓝 x) ∂(μ : Measure X)
      ≤ ∫⁻ x, ⨆ k, d k x ∂(μ : Measure X) := lintegral_mono hlow
    _ = ⨆ k, ∫⁻ x, d k x ∂(μ : Measure X) :=
        lintegral_iSup (fun k => (hd_lsc k).measurable) hd_mono
    _ ≤ _ := by
        refine iSup_le fun k => (g69h2_lsc_ennreal (hd_lsc k) h_opens).trans ?_
        refine liminf_le_liminf ?_
        filter_upwards [eventually_ge_atTop k] with n hn
        exact lintegral_mono (hdw k n hn)
