-- Prove2me | solution 1 for SSDConstraint.Optimality.U1_eq_uOfMeasure_unique
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:13:12.301209+00:00
-- url     : https://prove2.me/submissions/f30bd23e-db7e-47a9-abb9-bc4d65f2126a

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier

open MeasureTheory SSDConstraint.Optimality Filter Set Topology

theorem nl2_left_cont (μ : Measure ℝ) [IsFiniteMeasure μ] (b t : ℝ) :
    ContinuousWithinAt (fun s => μ.real (Icc s b)) (Iic t) t := by
  have h := tendsto_measure_biInter_gt (μ := μ) (a := (0:ℝ)) (s := fun δ => Icc (t - δ) b)
    (fun r _ => measurableSet_Icc.nullMeasurableSet)
    (fun i j _ hij => Icc_subset_Icc (by linarith) le_rfl) ⟨1, one_pos, measure_ne_top μ _⟩
  have hI : (⋂ r > (0:ℝ), Icc (t - r) b) = Icc t b := by
    ext x
    simp only [mem_iInter, mem_Icc]
    constructor
    · intro hx
      refine ⟨?_, (hx 1 one_pos).2⟩
      by_contra hlt
      push Not at hlt
      have := (hx ((t - x) / 2) (by linarith)).1
      linarith
    · intro hx r hr; exact ⟨by linarith [hx.1], hx.2⟩
  rw [hI] at h
  have hcomp : Tendsto (fun s : ℝ => t - s) (𝓝[<] t) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => t - s) (𝓝 t) (𝓝 (t - t)) :=
        (continuous_const.sub continuous_id).tendsto t
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_Ioi, sub_pos]; exact hs
  have h2 := h.comp hcomp
  have h3 : Tendsto (fun s => μ (Icc s b)) (𝓝[<] t) (𝓝 (μ (Icc t b))) := by
    refine h2.congr (fun s => ?_)
    simp only [Function.comp, sub_sub_cancel]
  have h4 := (ENNReal.tendsto_toReal (measure_ne_top μ (Icc t b))).comp h3
  apply continuousWithinAt_Iio_iff_Iic.1
  exact h4

theorem nl2_meas_unique (a b : ℝ) (μ1 μ2 : Measure ℝ) [IsFiniteMeasure μ1] [IsFiniteMeasure μ2]
    (h1 : μ1 (Icc a b)ᶜ = 0) (h2 : μ2 (Icc a b)ᶜ = 0)
    (heq : uOfMeasure μ1 b = uOfMeasure μ2 b) : μ1 = μ2 := by
  set g1 : ℝ → ℝ := fun s => μ1.real (Icc s b) with hg1
  set g2 : ℝ → ℝ := fun s => μ2.real (Icc s b) with hg2
  have hanti : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], Antitone (fun s => μ.real (Icc s b)) :=
    fun μ _ x y hxy => measureReal_mono (Icc_subset_Icc hxy le_rfl)
  have hderiv : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ),
      HasDerivWithinAt (fun u => ∫ x in u..b, μ.real (Icc x b)) (-(μ.real (Icc t b))) (Iic t) t :=
    fun μ _ t => intervalIntegral.integral_hasDerivWithinAt_left (s := Iic t) (t := Iic t)
      ((hanti μ).intervalIntegrable)
      ((hanti μ).measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
      (nl2_left_cont μ b t)
  have hlt : ∀ t < b, g1 t = g2 t := by
    intro t ht
    have hev : (fun u => ∫ x in u..b, μ1.real (Icc x b)) =ᶠ[𝓝[Iic t] t]
        (fun u => ∫ x in u..b, μ2.real (Icc x b)) := by
      have : ∀ᶠ u in 𝓝 t, u < b := eventually_lt_nhds ht
      filter_upwards [nhdsWithin_le_nhds this] with u hu
      have := congrFun heq u
      simp only [uOfMeasure, if_pos hu, neg_inj] at this
      exact this
    have d1 := hderiv μ1 t
    have d2 := (hderiv μ2 t).congr_of_eventuallyEq hev (hev.self_of_nhdsWithin (le_refl t))
    have := (uniqueDiffWithinAt_Iic t).eq_deriv _ d1 d2
    simpa [g1, g2] using this
  have hle : ∀ t ≤ b, g1 t = g2 t := by
    intro t ht
    rcases ht.lt_or_eq with ht | rfl
    · exact hlt t ht
    · have c1 := (continuousWithinAt_Iio_iff_Iic.2 (nl2_left_cont μ1 t t))
      have c2 := (continuousWithinAt_Iio_iff_Iic.2 (nl2_left_cont μ2 t t))
      have c1' : Tendsto g2 (𝓝[<] t) (𝓝 (g1 t)) :=
        c1.congr' (eventually_nhdsWithin_of_forall (fun s hs => hlt s hs))
      exact tendsto_nhds_unique c1' c2
  have hres : ∀ (μ : Measure ℝ), μ (Icc a b)ᶜ = 0 → ∀ s, MeasurableSet s →
      μ s = μ (s ∩ Icc a b) := by
    intro μ hμ s hs
    have hr : μ.restrict (Icc a b) = μ :=
      Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hμ |>.mono
        (fun x hx => by simpa using hx))
    conv_lhs => rw [← hr]
    rw [Measure.restrict_apply hs]
  have hIci : ∀ (μ : Measure ℝ), μ (Icc a b)ᶜ = 0 → ∀ t, μ (Ici t) = μ (Icc t b) := by
    intro μ hμ t
    rw [hres μ hμ _ measurableSet_Ici, hres μ hμ _ measurableSet_Icc]
    congr 1
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; tauto
  refine Measure.ext_of_Ici μ1 μ2 (fun t => ?_)
  rw [hIci μ1 h1, hIci μ2 h2]
  rcases le_or_gt t b with ht | ht
  · have := hle t ht
    simp only [g1, g2, Measure.real] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  · rw [Icc_eq_empty (not_le.2 ht), measure_empty, measure_empty]

theorem nl2_exists (a b : ℝ) (u : ℝ → ℝ) (hu : u ∈ U1 a b) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Icc a b)ᶜ = 0 ∧ u = uOfMeasure μ b := by
  obtain ⟨hconc, hmono, hzero, c, hc, hlin⟩ := hu
  set v : ℝ → ℝ := fun t => -u t with hv_def
  have hv : ConvexOn ℝ univ v := hconc.neg
  set f : ℝ → ℝ := fun x => derivWithin v (Ioi x) x with hf_def
  have hfd : ∀ x, HasDerivWithinAt v (f x) (Ioi x) x := fun x =>
    hv.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hfm : Monotone f := fun x y h =>
    hv.monotoneOn_rightDeriv (by simp) (by simp) h
  have hfb : ∀ x, b ≤ x → f x = 0 := by
    intro x hx
    have h0 : HasDerivWithinAt v 0 (Ioi x) x := by
      refine (hasDerivWithinAt_const x (Ioi x) (0:ℝ)).congr_of_eventuallyEq ?_ ?_
      · exact eventually_nhdsWithin_of_forall (fun y hy => by
          simp [v, hzero y (le_trans hx (le_of_lt hy))])
      · simp [v, hzero x hx]
    exact (uniqueDiffWithinAt_Ioi x).eq_deriv _ (hfd x) h0
  have hfa : ∀ x, x < a → f x = -c := by
    intro x hx
    have hw := ((((hasDerivAt_id x).sub_const a).const_mul c).const_add (u a)).neg
    rw [mul_one] at hw
    have h0 : HasDerivWithinAt v (-c) (Ioi x) x := by
      refine hw.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hx] with y hy
        simp [v, hlin y hy.2.le]
      · simp [v, hlin x hx.le]
    exact (uniqueDiffWithinAt_Ioi x).eq_deriv _ (hfd x) h0
  set F : StieltjesFunction ℝ := hfm.stieltjesFunction with hF_def
  have hF : ∀ x, F x = Function.rightLim f x := fun x => rfl
  have hFb : ∀ x, b ≤ x → F x = 0 := by
    intro x hx
    have h1 := hfm.le_rightLim (le_refl x)
    have h2 := hfm.rightLim_le (show x < x + 1 by linarith)
    rw [hF]
    rw [hfb x hx] at h1; rw [hfb (x+1) (by linarith)] at h2
    linarith
  have hFa : ∀ x, x < a → F x = -c := by
    intro x hx
    have h1 := hfm.le_rightLim (le_refl x)
    have h2 := hfm.rightLim_le (show x < (x + a) / 2 by linarith)
    rw [hF]
    rw [hfa x hx] at h1; rw [hfa ((x + a) / 2) (by linarith)] at h2
    linarith
  have htop : Tendsto F atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop b] with x hx
      exact (hFb x hx).symm)
  have hbot : Tendsto F atBot (𝓝 (-c)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_lt_atBot a] with x hx
      exact (hFa x hx).symm)
  have hfin : IsFiniteMeasure F.measure := F.isFiniteMeasure hbot htop
  refine ⟨F.measure, hfin, ?_, ?_⟩
  · have hsub : (Icc a b)ᶜ ⊆ Iio a ∪ Ioi b := by
      intro x hx
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [F.measure_Iio hbot a]
      have : Function.leftLim F a = -c := by
        refine leftLim_eq_of_tendsto ?_
        exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
          (fun x hx => (hFa x hx).symm))
      rw [this, sub_self, ENNReal.ofReal_zero]
    · rw [F.measure_Ioi htop b, hFb b le_rfl, sub_self, ENNReal.ofReal_zero]
  · funext t
    unfold uOfMeasure
    split_ifs with htb
    · -- real measure of Icc
      have hreal : ∀ τ ∈ uIcc t b, F.measure.real (Icc τ b) = -Function.leftLim F τ := by
        intro τ hτ
        have hτb : τ ≤ b := by
          rw [uIcc_of_le htb.le] at hτ; exact hτ.2
        rw [Measure.real, F.measure_Icc, hFb b le_rfl, zero_sub, ENNReal.toReal_ofReal]
        have := F.mono.leftLim_le (le_refl τ)
        have h2 := F.mono hτb
        rw [hFb b le_rfl] at h2
        linarith
      rw [intervalIntegral.integral_congr hreal]
      -- a.e. equality with -f
      have hD : Set.Countable ({x | Function.leftLim F x ≠ F x} ∪ {x | ¬ ContinuousAt f x}) :=
        F.countable_leftLim_ne.union hfm.countable_not_continuousAt
      have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc t b → -Function.leftLim F x = -f x := by
        have := (measure_eq_zero_iff_ae_notMem.1 (hD.measure_zero volume))
        filter_upwards [this] with x hx _
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hx
        rw [hx.1, hF, hx.2.continuousWithinAt.rightLim_eq]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg]
      have hcont : Continuous v := (continuousOn_univ.1 (hconc.continuousOn isOpen_univ)).neg
      rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htb.le hcont.continuousOn
        (fun x _ => hfd x) hfm.intervalIntegrable]
      simp [v, hzero b le_rfl]
    · exact hzero t (not_lt.1 htb)

theorem solution (a b : ℝ) :
    ∀ u ∈ U1 a b, ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Icc a b)ᶜ = 0 ∧
      u = uOfMeasure μ b := by
  intro u hu
  obtain ⟨μ, hμf, hμs, hμu⟩ := nl2_exists a b u hu
  refine ⟨μ, ⟨hμf, hμs, hμu⟩, fun ν ⟨hνf, hνs, hνu⟩ => ?_⟩
  exact nl2_meas_unique a b ν μ hνs hμs (hνu.symm.trans hμu)
