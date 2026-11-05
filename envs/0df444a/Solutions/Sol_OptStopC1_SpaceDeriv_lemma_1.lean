-- Prove2me | solution 1 for OptStopC1.SpaceDeriv.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:03:55.11862+00:00
-- url     : https://prove2.me/submissions/0fa666e9-a078-4467-ad00-d84e278857e1

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

open OptStopC1.SpaceDeriv in
theorem solution
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (hF : IsStrongFeller X P) (ε : ℝ≥0) (hε : 0 < ε) :
    UpperSemicontinuous
      (fun x : State d => P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x D ω}) := by
  -- the delayed hitting time δ + σ_D ∘ θ_δ = inf {t > δ : X_t ∈ D}
  let τd : ℝ≥0 → State d → Ω → ℝ≥0∞ := fun δ x ω =>
    sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | δ < t ∧ X x t ω ∈ D})
  have hstop := hX.2.2.2.2.2.2.1 D (Or.inr hD)
  -- measurability of {c ≤ T} for a stopping time T
  have hmeasGe : ∀ (T : Ω → ℝ≥0∞), IsStoppingTime 𝔽 T → ∀ c : ℝ≥0,
      MeasurableSet {ω | (c : ℝ≥0∞) ≤ T ω} := by
    intro T hT c
    have hlt : MeasurableSet {ω | T ω < ((c : ℝ≥0) : WithTop ℝ≥0)} :=
      𝔽.le c _ (hT.measurableSet_lt c)
    have hset : {ω | (c : ℝ≥0∞) ≤ T ω} = {ω | T ω < ((c : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff]
      exact not_lt.symm
    rw [hset]
    exact hlt.compl
  -- Step 1: for 0 < δ < ε, x ↦ P(τ_δ ≥ ε) is continuous (strong Markov + strong Feller).
  have hcontδ : ∀ δ : ℝ≥0, 0 < δ → δ < ε →
      Continuous (fun x => P {ω | (ε : ℝ≥0∞) ≤ τd δ x ω}) := by
    intro δ hδ hδε
    set c : ℝ≥0 := ε - δ with hcdef
    have hc : 0 < c := tsub_pos_of_lt hδε
    let Φ : (ℝ≥0 → State d) → ℝ := fun path =>
      if (c : ℝ≥0∞) ≤ sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | 0 < t ∧ path t ∈ D})
      then 1 else 0
    have hΦy : ∀ y, (fun ω => Φ (fun t => X y t ω)) =
        {ω | (c : ℝ≥0∞) ≤ hittingTime X y D ω}.indicator 1 := by
      intro y; ext ω
      simp only [Φ, Set.indicator_apply, mem_ofPred_eq, Pi.one_apply, hittingTime]
    have hmy : ∀ y, MeasurableSet {ω | (c : ℝ≥0∞) ≤ hittingTime X y D ω} :=
      fun y => hmeasGe _ (hstop y).2.1 c
    have hFy : ∀ y, ∫ ω, Φ (fun t => X y t ω) ∂P =
        (P {ω | (c : ℝ≥0∞) ≤ hittingTime X y D ω}).toReal := by
      intro y
      rw [hΦy y, integral_indicator_one (hmy y), measureReal_def]
    -- the shift identity
    have hkey : ∀ x ω, ((c : ℝ≥0∞) ≤
        sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | 0 < t ∧ X x (δ + t) ω ∈ D})) ↔
        ((ε : ℝ≥0∞) ≤ τd δ x ω) := by
      intro x ω
      simp only [τd, le_sInf_iff, forall_mem_image, mem_ofPred_eq, ENNReal.coe_le_coe]
      constructor
      · rintro h s ⟨hδs, hXs⟩
        have h1 : ε - δ ≤ s - δ :=
          h (x := s - δ) ⟨tsub_pos_of_lt hδs, by rwa [add_tsub_cancel_of_le hδs.le]⟩
        exact (tsub_le_tsub_iff_right hδs.le).1 h1
      · rintro h t ⟨ht, hXt⟩
        have h1 : ε ≤ δ + t := h (x := δ + t) ⟨lt_add_of_pos_right _ ht, hXt⟩
        exact tsub_le_iff_left.2 h1
    have hshift : ∀ x, (fun ω => Φ (fun t => X x ((fun _ => δ) ω + t) ω)) =
        {ω | (ε : ℝ≥0∞) ≤ τd δ x ω}.indicator 1 := by
      intro x; ext ω
      simp only [Φ, Set.indicator_apply, mem_ofPred_eq, Pi.one_apply]
      rw [if_congr (hkey x ω) rfl rfl]
    have hmshift : ∀ x, MeasurableSet {ω | (ε : ℝ≥0∞) ≤ τd δ x ω} :=
      fun x => hmeasGe _ ((hstop x).2.2 δ) ε
    -- F(y) = P_y(σ_D ≥ ε - δ)
    let F : State d → ℝ := fun y => (P {ω | (c : ℝ≥0∞) ≤ hittingTime X y D ω}).toReal
    have hFmeas : Measurable F :=
      (hX.2.2.2.2.2.2.2 D (Or.inr hD) c hc).ennreal_toReal
    have hFbdd : Bornology.IsBounded (Set.range F) := by
      refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨ENNReal.toReal_nonneg, by
        have := prob_le_one (μ := P) (s := {ω | (c : ℝ≥0∞) ≤ hittingTime X y D ω})
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
    have hΦbdd : Bornology.IsBounded (Set.range Φ) := by
      refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
      rintro _ ⟨path, rfl⟩
      simp only [Φ]
      split_ifs <;> simp
    have hρ : IsStoppingTime 𝔽 (fun _ : Ω => ((δ : ℝ≥0) : ℝ≥0∞)) := isStoppingTime_const 𝔽 _
    have hrep : ∀ x, (P {ω | (ε : ℝ≥0∞) ≤ τd δ x ω}).toReal = ∫ ω, F (X x δ ω) ∂P := by
      intro x
      have hSM := hX.2.2.2.2.1 x (fun _ => δ) hρ Φ hΦbdd
        (fun y => by rw [hΦy y]; exact measurable_one.indicator (hmy y))
        (by
          have : (fun y => ∫ ω, Φ (fun t => X y t ω) ∂P) = F := funext hFy
          rw [this]; exact hFmeas)
        (by rw [hshift x]; exact measurable_one.indicator (hmshift x))
      have hint := integral_congr_ae hSM
      rw [integral_condExp hρ.measurableSpace_le] at hint
      rw [hshift x, integral_indicator_one (hmshift x), measureReal_def] at hint
      rw [hint]
      exact integral_congr_ae (Eventually.of_forall fun ω => hFy _)
    have hcont := hF δ hδ F hFmeas hFbdd
    have heq : (fun x => P {ω | (ε : ℝ≥0∞) ≤ τd δ x ω}) =
        fun x => ENNReal.ofReal (∫ ω, F (X x δ ω) ∂P) := by
      funext x
      rw [← hrep x, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [heq]
    exact ENNReal.continuous_ofReal.comp hcont
  -- Step 2: δ_n ↓ 0 and P(σ_D ≥ ε) is the decreasing limit of P(τ_{δ_n} ≥ ε).
  let δs : ℕ → ℝ≥0 := fun n => ε / ((n : ℝ≥0) + 2)
  have hδpos : ∀ n, 0 < δs n := fun n => div_pos hε (by positivity)
  have hδlt : ∀ n, δs n < ε := fun n =>
    div_lt_self hε (by exact_mod_cast (show 1 < n + 2 by omega))
  have hδsmall : ∀ t : ℝ≥0, 0 < t → ∃ n, δs n < t := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt (ε / t)
    refine ⟨n, ?_⟩
    have hn' : ε < n * t := (div_lt_iff₀ ht).1 hn
    show ε / ((n : ℝ≥0) + 2) < t
    rw [div_lt_iff₀ (by positivity)]
    calc ε < n * t := hn'
      _ = t * n := mul_comm _ _
      _ ≤ t * (n + 2) := mul_le_mul_right (le_add_of_nonneg_right zero_le) t
  have hδanti : Antitone δs := by
    intro m n hmn
    simp only [δs]
    gcongr
  have hinter : ∀ x, {ω | (ε : ℝ≥0∞) ≤ hittingTime X x D ω} =
      ⋂ n, {ω | (ε : ℝ≥0∞) ≤ τd (δs n) x ω} := by
    intro x
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h n
      exact h.trans (sInf_le_sInf (image_mono fun t ht => ⟨lt_trans (hδpos n) ht.1, ht.2⟩))
    · intro h
      by_contra hlt
      have hlt' : hittingTime X x D ω < ε := not_le.1 hlt
      obtain ⟨_, ⟨t, ⟨ht0, htD⟩, rfl⟩, htε⟩ := sInf_lt_iff.1 hlt'
      obtain ⟨n, hn⟩ := hδsmall t ht0
      have h2 : τd (δs n) x ω ≤ t := sInf_le ⟨t, ⟨hn, htD⟩, rfl⟩
      exact absurd (lt_of_le_of_lt ((h n).trans h2) htε) (lt_irrefl _)
  have hEanti : ∀ x, Antitone (fun n => {ω | (ε : ℝ≥0∞) ≤ τd (δs n) x ω}) := by
    intro x m n hmn ω hω
    have hω' : (ε : ℝ≥0∞) ≤ τd (δs n) x ω := hω
    show (ε : ℝ≥0∞) ≤ τd (δs m) x ω
    exact le_trans hω' (sInf_le_sInf (image_mono fun t (ht : δs m < t ∧ X x t ω ∈ D) =>
      (⟨lt_of_le_of_lt (hδanti hmn) ht.1, ht.2⟩ : δs n < t ∧ X x t ω ∈ D)))
  -- Step 3: an infimum of continuous functions is upper semicontinuous.
  intro x y hy
  have hlim : Tendsto (fun n => P {ω | (ε : ℝ≥0∞) ≤ τd (δs n) x ω}) atTop
      (𝓝 (P (⋂ n, {ω | (ε : ℝ≥0∞) ≤ τd (δs n) x ω}))) :=
    tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hmeasGe _ ((hstop x).2.2 (δs n)) ε).nullMeasurableSet) (hEanti x)
    ⟨0, measure_ne_top _ _⟩
  rw [← hinter x] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hy)).exists
  have hc := (hcontδ (δs n) (hδpos n) (hδlt n)).tendsto x
  filter_upwards [hc.eventually (gt_mem_nhds hn)] with x' hx'
  refine lt_of_le_of_lt (measure_mono ?_) hx'
  rw [hinter x']
  exact iInter_subset _ n
