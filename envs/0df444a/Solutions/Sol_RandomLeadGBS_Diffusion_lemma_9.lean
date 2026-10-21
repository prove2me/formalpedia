-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:25:20.344902+00:00
-- url     : https://prove2.me/submissions/bc2c7481-44ca-49b6-b7bc-efd600502193

import Mathlib

open Filter Topology MeasureTheory Set

namespace GBSLemma9

/-- `μ ≤st ν` on half-lines `(x, ∞)` passes to closed half-lines `[a, ∞)`. -/
lemma ici_le (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (a : ℝ) : μ (Ici a) ≤ ν (Ici a) := by
  have hset : Ici a = ⋂ n : ℕ, Ioi (a - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [mem_Ici, mem_iInter, mem_Ioi]
    constructor
    · intro hx n
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      by_contra hlt
      push_neg at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have := hx n
      linarith
  have hanti : Antitone (fun n : ℕ => Ioi (a - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn x hx
    simp only [mem_Ioi] at *
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  rw [hset, hanti.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩,
    hanti.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact iInf_mono fun n => h _

/-- `μ ≤st ν` gives `μ S ≤ ν S` for every upper set `S ⊆ ℝ`. -/
lemma upper_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (S : Set ℝ) (hS : IsUpperSet S) : μ S ≤ ν S := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · simp [hE]
  by_cases hb : BddBelow S
  · set a := sInf S with ha
    by_cases haS : a ∈ S
    · have : S = Ici a := by
        ext y
        constructor
        · intro hy; exact csInf_le hb hy
        · intro hy; exact hS hy haS
      rw [this]; exact ici_le μ ν h a
    · have : S = Ioi a := by
        ext y
        constructor
        · intro hy
          have h1 : a ≤ y := csInf_le hb hy
          rcases h1.lt_or_eq with h2 | h2
          · exact h2
          · exact absurd (h2 ▸ hy) haS
        · intro hy
          obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
          exact hS hzy.le hz
      rw [this]; exact h a
  · have : S = univ := by
      ext y
      simp only [mem_univ, iff_true]
      rw [not_bddBelow_iff] at hb
      obtain ⟨z, hz, hzy⟩ := hb y
      exact hS hzy.le hz
    rw [this, measure_univ, measure_univ]

lemma lower_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (S : Set ℝ) (hS : IsLowerSet S) : ν S ≤ μ S := by
  have hU : IsUpperSet Sᶜ := hS.compl
  have hm : MeasurableSet Sᶜ := hU.ordConnected.measurableSet
  have h1 := upper_le μ ν h Sᶜ hU
  have e1 : μ S = 1 - μ Sᶜ := by
    rw [← prob_compl_eq_one_sub hm, compl_compl]
  have e2 : ν S = 1 - ν Sᶜ := by
    rw [← prob_compl_eq_one_sub hm, compl_compl]
  rw [e1, e2]
  exact tsub_le_tsub_left h1 _

/-- Monotone nonnegative functions: stochastic order gives order of integrals. -/
lemma mono_nonneg (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (f : ℝ → ℝ) (hf : Monotone f) (hnn : 0 ≤ f)
    (hfν : Integrable f ν) : ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν := by
  have hmeas := hf.measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_mono hfν.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hnn) hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hnn) hmeas.aemeasurable]
  refine lintegral_mono fun t => upper_le μ ν h _ ?_
  intro a b hab ha
  exact lt_of_lt_of_le ha (hf hab)

lemma anti_nonneg (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (f : ℝ → ℝ) (hf : Antitone f) (hnn : 0 ≤ f)
    (hfμ : Integrable f μ) : ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
  have hmeas := hf.measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_mono hfμ.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hnn) hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hnn) hmeas.aemeasurable]
  refine lintegral_mono fun t => lower_le μ ν h _ ?_
  intro a b hab ha
  exact lt_of_lt_of_le ha (hf hab)

/-- Monotone integrable functions: stochastic order gives order of integrals. -/
lemma mono_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ (Ioi x) ≤ ν (Ioi x)) (u : ℝ → ℝ) (hu : Monotone u)
    (huμ : Integrable u μ) (huν : Integrable u ν) : ∫ x, u x ∂μ ≤ ∫ x, u x ∂ν := by
  have hsplit : ∀ m : Measure ℝ, Integrable u m →
      ∫ x, u x ∂m = ∫ x, max (u x) 0 ∂m - ∫ x, max (-u x) 0 ∂m := by
    intro m hm
    rw [← integral_sub hm.pos_part hm.neg_part]
    congr 1; funext x
    exact (max_zero_sub_max_neg_zero_eq_self (u x)).symm
  rw [hsplit μ huμ, hsplit ν huν]
  have h1 : ∫ x, max (u x) 0 ∂μ ≤ ∫ x, max (u x) 0 ∂ν :=
    mono_nonneg μ ν h _ (fun a b hab => max_le_max (hu hab) le_rfl)
      (fun x => le_max_right _ _) huν.pos_part
  have h2 : ∫ x, max (-u x) 0 ∂ν ≤ ∫ x, max (-u x) 0 ∂μ :=
    anti_nonneg μ ν h _ (fun a b hab => max_le_max (neg_le_neg (hu hab)) le_rfl)
      (fun x => le_max_right _ _) huμ.neg_part
  linarith

end GBSLemma9

open GBSLemma9

theorem solution (μ ν : ℝ → Measure ℝ) (μA : Measure ℝ)
    (hμ : ∀ r, 0 < r → IsProbabilityMeasure (μ r))
    (hν : ∀ r, 0 < r → IsProbabilityMeasure (ν r))
    (hμA : IsProbabilityMeasure μA)
    (h32 : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun r => ∫ x, g x ∂(μ r)) atTop (𝓝 (∫ x, g x ∂μA)))
    (hA : Integrable (fun x : ℝ => x) μA)
    (h33p : Tendsto (fun r => ∫ x, max x 0 ∂(μ r)) atTop (𝓝 (∫ x, max x 0 ∂μA)))
    (h33m : Tendsto (fun r => ∫ x, max (-x) 0 ∂(μ r)) atTop (𝓝 (∫ x, max (-x) 0 ∂μA)))
    (hst : ∀ r, 0 < r → ∀ x : ℝ, μ r (Set.Ioi x) ≤ ν r (Set.Ioi x))
    (hint : ∀ r, 0 < r →
      Integrable (fun x : ℝ => x) (μ r) ∧ Integrable (fun x : ℝ => x) (ν r))
    (hmean : Tendsto (fun r => ∫ x, x ∂(ν r) - ∫ x, x ∂(μ r)) atTop (𝓝 0)) :
    (∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun r => ∫ x, g x ∂(ν r)) atTop (𝓝 (∫ x, g x ∂μA))) ∧
    Tendsto (fun r => ∫ x, max x 0 ∂(ν r)) atTop (𝓝 (∫ x, max x 0 ∂μA)) ∧
    Tendsto (fun r => ∫ x, max (-x) 0 ∂(ν r)) atTop (𝓝 (∫ x, max (-x) 0 ∂μA)) := by
  have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  set D : ℝ → ℝ := fun r => ∫ x, x ∂(ν r) - ∫ x, x ∂(μ r) with hD
  -- Bounds on the positive and negative parts.
  have hparts : ∀ r, 0 < r →
      0 ≤ ∫ x, max x 0 ∂(ν r) - ∫ x, max x 0 ∂(μ r) ∧
      ∫ x, max x 0 ∂(ν r) - ∫ x, max x 0 ∂(μ r) ≤ D r ∧
      0 ≤ ∫ x, max (-x) 0 ∂(μ r) - ∫ x, max (-x) 0 ∂(ν r) ∧
      ∫ x, max (-x) 0 ∂(μ r) - ∫ x, max (-x) 0 ∂(ν r) ≤ D r := by
    intro r hr
    haveI := hμ r hr
    haveI := hν r hr
    obtain ⟨iμ, iν⟩ := hint r hr
    have h1 : ∫ x, max x 0 ∂(μ r) ≤ ∫ x, max x 0 ∂(ν r) :=
      mono_le _ _ (hst r hr) (fun x => max x 0) (fun a b hab => max_le_max hab le_rfl)
        iμ.pos_part iν.pos_part
    have h2 : ∫ x, -max (-x) 0 ∂(μ r) ≤ ∫ x, -max (-x) 0 ∂(ν r) :=
      mono_le _ _ (hst r hr) (fun x => -max (-x) 0)
        (fun a b hab => neg_le_neg (max_le_max (neg_le_neg hab) le_rfl))
        iμ.neg_part.neg iν.neg_part.neg
    rw [integral_neg, integral_neg] at h2
    have e : ∀ m : Measure ℝ, Integrable (fun x : ℝ => x) m →
        ∫ x, x ∂m = ∫ x, max x 0 ∂m - ∫ x, max (-x) 0 ∂m := by
      intro m hm
      rw [← integral_sub hm.pos_part hm.neg_part]
      congr 1; funext x
      exact (max_zero_sub_max_neg_zero_eq_self x).symm
    have eD : D r = (∫ x, max x 0 ∂(ν r) - ∫ x, max x 0 ∂(μ r)) +
        (∫ x, max (-x) 0 ∂(μ r) - ∫ x, max (-x) 0 ∂(ν r)) := by
      simp only [hD]; rw [e _ iμ, e _ iν]; ring
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · -- positive part
    have h0 : Tendsto (fun r => ∫ x, max x 0 ∂(ν r) - ∫ x, max x 0 ∂(μ r)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hmean
      · filter_upwards [hpos] with r hr using (hparts r hr).1
      · filter_upwards [hpos] with r hr using (hparts r hr).2.1
    have := h33p.add h0
    simp only [add_zero, add_sub_cancel] at this
    exact this
  · -- negative part
    have h0 : Tendsto (fun r => ∫ x, max (-x) 0 ∂(μ r) - ∫ x, max (-x) 0 ∂(ν r)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hmean
      · filter_upwards [hpos] with r hr using (hparts r hr).2.2.1
      · filter_upwards [hpos] with r hr using (hparts r hr).2.2.2
    have := h33m.sub h0
    simp only [sub_zero, sub_sub_cancel] at this
    exact this
  -- weak convergence
  let μp : ℝ → ProbabilityMeasure ℝ := fun r =>
    if h : 0 < r then ⟨μ r, hμ r h⟩ else ⟨μA, hμA⟩
  let νp : ℝ → ProbabilityMeasure ℝ := fun r =>
    if h : 0 < r then ⟨ν r, hν r h⟩ else ⟨μA, hμA⟩
  let A : ProbabilityMeasure ℝ := ⟨μA, hμA⟩
  have hμp : ∀ r, 0 < r → (μp r : Measure ℝ) = μ r := by
    intro r hr; simp [μp, hr]
  have hνp : ∀ r, 0 < r → (νp r : Measure ℝ) = ν r := by
    intro r hr; simp [νp, hr]
  have hμconv : Tendsto μp atTop (𝓝 A) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    refine (h32 g).congr' ?_
    filter_upwards [hpos] with r hr
    rw [hμp r hr]
  have hνconv : Tendsto νp atTop (𝓝 A) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hfL
    have h1 := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hμconv) f hfb hfL
    obtain ⟨L, hL⟩ := hfL
    obtain ⟨C, hC⟩ := hfb
    have hfint : ∀ m : Measure ℝ, IsFiniteMeasure m → Integrable f m := by
      intro m _
      refine Integrable.of_bound hL.continuous.aestronglyMeasurable (‖f 0‖ + C)
        (Eventually.of_forall fun x => ?_)
      have := hC x 0
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (f x) (f 0)
      linarith
    have hdiff : ∀ r, 0 < r →
        |∫ x, f x ∂(ν r) - ∫ x, f x ∂(μ r)| ≤ (L : ℝ) * D r := by
      intro r hr
      haveI := hμ r hr
      haveI := hν r hr
      obtain ⟨iμ, iν⟩ := hint r hr
      have fμ := hfint (μ r) inferInstance
      have fν := hfint (ν r) inferInstance
      have hmono1 : Monotone (fun x => f x + (L : ℝ) * x) := by
        intro a b hab
        have := hL.dist_le_mul b a
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)] at this
        have := neg_abs_le (f b - f a)
        nlinarith
      have hmono2 : Monotone (fun x => (L : ℝ) * x - f x) := by
        intro a b hab
        have := hL.dist_le_mul b a
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)] at this
        have := le_abs_self (f b - f a)
        nlinarith
      have k1 := mono_le _ _ (hst r hr) _ hmono1 (fμ.add (iμ.const_mul _)) (fν.add (iν.const_mul _))
      have k2 := mono_le _ _ (hst r hr) _ hmono2 ((iμ.const_mul _).sub fμ) ((iν.const_mul _).sub fν)
      rw [integral_add fμ (iμ.const_mul _), integral_add fν (iν.const_mul _),
        integral_const_mul, integral_const_mul] at k1
      rw [integral_sub (iμ.const_mul _) fμ, integral_sub (iν.const_mul _) fν,
        integral_const_mul, integral_const_mul] at k2
      rw [abs_le]
      simp only [hD]
      constructor <;> nlinarith
    have h0 : Tendsto (fun r => ∫ x, f x ∂(νp r : Measure ℝ) - ∫ x, f x ∂(μp r : Measure ℝ))
        atTop (𝓝 0) := by
      have hLD : Tendsto (fun r => (L : ℝ) * D r) atTop (𝓝 0) := by
        simpa using hmean.const_mul (L : ℝ)
      refine squeeze_zero_norm' ?_ hLD
      filter_upwards [hpos] with r hr
      rw [hμp r hr, hνp r hr, Real.norm_eq_abs]
      exact hdiff r hr
    have := h1.add h0
    simp only [add_zero, add_sub_cancel] at this
    exact this
  intro g
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hνconv) g
  refine this.congr' ?_
  filter_upwards [hpos] with r hr
  rw [hνp r hr]
