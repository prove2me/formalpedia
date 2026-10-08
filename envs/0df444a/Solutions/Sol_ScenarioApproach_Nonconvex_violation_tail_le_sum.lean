-- Prove2me | solution 1 for ScenarioApproach.Nonconvex.violation_tail_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:13:40.662511+00:00
-- url     : https://prove2.me/submissions/6d11e096-80ce-4d8f-b924-7d5002a67226

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
import Definitions.Def_ScenarioApproach_Nonconvex_supportSet



namespace ScenarioApproach.Nonconvex

open MeasureTheory

lemma vt_meas_viol {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2}) :
    Measurable (fun θ => violation P Θδ θ) := by
  unfold violation violationSet
  have := measurable_measure_prodMk_left (ν := P) hmeas.compl
  exact this.ennreal_toReal

lemma vt_viol_le_one {Θ Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ) (θ : Θ) :
    violation P Θδ θ ≤ 1 := by
  unfold violation
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := violationSet Θδ θ))
  simpa using this

lemma vt_sol_congr {Θ Δ : Type*} {N : ℕ} (f : Θ → ℝ) (Θδ : Δ → Set Θ) (ω ω' : Fin N → Δ)
    (I I' : Finset (Fin N)) (h : feasibleOn Θδ ω I = feasibleOn Θδ ω' I') (θ : Θ) :
    IsSolutionOn f Θδ ω I θ ↔ IsSolutionOn f Θδ ω' I' θ := by
  unfold IsSolutionOn; rw [h]

/-- slice bound -/
lemma vt_slice {Θ Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ) (θ : Θ)
    (hm : MeasurableSet (violationSet Θδ θ)) (ι : Type*) [Fintype ι] (c : ℝ)
    (hc : c < violation P Θδ θ) :
    Measure.pi (fun _ : ι => P) (Set.pi Set.univ (fun _ => {δ | θ ∈ Θδ δ}))
      ≤ ENNReal.ofReal ((1 - c) ^ Fintype.card ι) := by
  rw [Measure.pi_pi]
  have h1 : P {δ | θ ∈ Θδ δ} = 1 - P (violationSet Θδ θ) := by
    rw [← prob_compl_eq_one_sub hm]
    congr 1; ext δ; simp [violationSet]
  have h2 : P {δ | θ ∈ Θδ δ} ≤ ENNReal.ofReal (1 - c) := by
    rw [h1]
    have hv : P (violationSet Θδ θ) = ENNReal.ofReal (violation P Θδ θ) := by
      unfold violation; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hv, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by unfold violation; positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [Finset.prod_const, Finset.card_univ]
  have hle : 0 ≤ 1 - c ∨ 1 - c < 0 := le_or_gt 0 (1 - c)
  rcases hle with hle | hle
  · rw [ENNReal.ofReal_pow hle]; exact pow_le_pow_left' h2 _
  · -- then 1 - c < 0 so ofReal(1-c) = 0, P ... ≤ 0
    have : P {δ | θ ∈ Θδ δ} = 0 := le_antisymm (h2.trans (by simp [ENNReal.ofReal_eq_zero.2 hle.le])) bot_le
    rw [this]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · simp [h0]
    · rw [zero_pow h0.ne']; exact zero_le


lemma vt_card_compl {N : ℕ} (J : Finset (Fin N)) :
    Fintype.card {i : Fin N // i ∉ J} = N - J.card := by
  simp [Fintype.card_subtype_compl]

lemma vt_J {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (J : Finset (Fin N)) (c : ℝ) (G : (∀ _ : {i // i ∈ J}, Δ) → Θ) (hG : Measurable G)
    (E : Set (Fin N → Δ))
    (hE : ∀ ω ∈ E, c < violation P Θδ (G (fun i => ω i.1)) ∧
      ∀ i ∉ J, G (fun i => ω i.1) ∈ Θδ (ω i)) :
    Measure.pi (fun _ : Fin N => P) E ≤ ENNReal.ofReal ((1 - c) ^ (N - J.card)) := by
  classical
  set T : Set ((∀ _ : {i // i ∈ J}, Δ) × (∀ _ : {i // i ∉ J}, Δ)) :=
    {p | c < violation P Θδ (G p.1) ∧ ∀ i, G p.1 ∈ Θδ (p.2 i)} with hTdef
  have hT : MeasurableSet T := by
    have : T = {p | c < violation P Θδ (G p.1)} ∩ ⋂ i, {p | (G p.1, p.2 i) ∈ {p : Θ × Δ | p.1 ∈ Θδ p.2}} := by
      ext p; simp [T]
    rw [this]
    refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun i => ?_)
    · exact measurableSet_lt measurable_const ((vt_meas_viol P Θδ hmeas).comp (hG.comp measurable_fst))
    · exact hmeas.preimage ((hG.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => P) (fun i => i ∈ J)
  calc Measure.pi (fun _ : Fin N => P) E
      ≤ Measure.pi (fun _ : Fin N => P)
          ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Δ) (fun i => i ∈ J)) ⁻¹' T) := by
        apply measure_mono
        intro ω hω
        obtain ⟨h1, h2⟩ := hE ω hω
        exact ⟨h1, fun i => h2 i.1 i.2⟩
    _ = ((Measure.pi fun _ : {i // i ∈ J} => P).prod (Measure.pi fun _ : {i // i ∉ J} => P)) T :=
        by convert hmp.measure_preimage hT.nullMeasurableSet
    _ = ∫⁻ x, (Measure.pi fun _ : {i // i ∉ J} => P) (Prod.mk x ⁻¹' T)
          ∂(Measure.pi fun _ : {i // i ∈ J} => P) := Measure.prod_apply hT
    _ ≤ ∫⁻ _x, ENNReal.ofReal ((1 - c) ^ (N - J.card)) ∂(Measure.pi fun _ : {i // i ∈ J} => P) := by
        apply lintegral_mono
        intro x
        by_cases hx : c < violation P Θδ (G x)
        · have hsub : Prod.mk x ⁻¹' T ⊆ Set.pi Set.univ (fun _ => {δ | G x ∈ Θδ δ}) := by
            intro y hy i _; exact hy.2 i
          refine (measure_mono hsub).trans ?_
          have hm : MeasurableSet (violationSet Θδ (G x)) := by
            have := (measurable_prodMk_left (β := Δ) (x := G x)) hmeas.compl
            exact this
          have := vt_slice P Θδ (G x) hm {i // i ∉ J} c hx
          rwa [vt_card_compl] at this
        · have : Prod.mk x ⁻¹' T = ∅ := by
            ext y; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro hy; exact hx hy.1
          dsimp only; rw [this, measure_empty]; exact zero_le
    _ = ENNReal.ofReal ((1 - c) ^ (N - J.card)) := by
        rw [lintegral_const, measure_univ, mul_one]


lemma vt_comb (N : ℕ) (g : ℕ → ℝ) :
    ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N), g J.card
      = ∑ k ∈ Finset.range N, (N.choose k : ℝ) * g k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range N)
    (fun J hJ => Finset.mem_range.2 (Finset.mem_filter.1 hJ).2)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_congr rfl (fun J hJ => by rw [(Finset.mem_filter.1 hJ).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.univ.filter (fun J : Finset (Fin N) => J.card < N)).filter (fun J => J.card = k)
      = Finset.powersetCard k Finset.univ := by
    ext J; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    have := Finset.mem_range.1 hk
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem vt_core {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (ε : ℕ → ℝ) (hε : ∀ k ≤ N, ε k ∈ Set.Icc (0 : ℝ) 1) (hεN : ε N = 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε (alg ω).card < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - ε k) ^ (N - k)) := by
  classical
  have hsolJ : ∀ ω, IsUniqueSolutionOn f Θδ ω (alg ω) (θstar ω) := by
    intro ω; obtain ⟨θ, h1, h2⟩ := halg ω
    have : θ = θstar ω := (hθstar ω).2 θ h1.1
    rwa [← this]
  have hEJ : ∀ J : Finset (Fin N),
      Measure.pi (fun _ : Fin N => P) {ω | alg ω = J ∧ ε J.card < violation P Θδ (θstar ω)}
        ≤ ENNReal.ofReal ((1 - ε J.card) ^ (N - J.card)) := by
    intro J
    rcases J.eq_empty_or_nonempty with h0 | ⟨j0, hj0⟩
    · by_cases hex : ∃ ω0, alg ω0 = J
      · obtain ⟨ω0, hω0⟩ := hex
        apply vt_J P Θδ N hmeas J _ (fun _ => θstar ω0) measurable_const
        rintro ω ⟨hω, hc⟩
        have h0' := hsolJ ω0; rw [hω0] at h0'
        have h1' := hsolJ ω; rw [hω] at h1'
        have heq : θstar ω0 = θstar ω := h1'.2 _
          ((vt_sol_congr f Θδ ω0 ω J J (by subst h0; ext θ; simp [feasibleOn]) _).1 h0'.1)
        rw [heq]; exact ⟨hc, fun i _ => (hθstar ω).1.1 i (Finset.mem_univ _)⟩
      · push_neg at hex
        have : {ω | alg ω = J ∧ ε J.card < violation P Θδ (θstar ω)} = ∅ := by
          ext ω; simp [hex ω]
        rw [this, measure_empty]; exact zero_le
    · let G : (∀ _ : {i // i ∈ J}, Δ) → Θ :=
        fun x => θstar (fun i => if h : i ∈ J then x ⟨i, h⟩ else x ⟨j0, hj0⟩)
      have hG : Measurable G := by
        apply hθstar_meas.comp
        apply measurable_pi_lambda
        intro i
        by_cases h : i ∈ J
        · simp only [h, dite_true]; exact measurable_pi_apply _
        · simp only [h, dite_false]; exact measurable_pi_apply _
      apply vt_J P Θδ N hmeas J _ G hG
      rintro ω ⟨hω, hc⟩
      have h1' := hsolJ ω; rw [hω] at h1'
      set ω' : Fin N → Δ := fun i => if h : i ∈ J then ω i else ω j0 with hω'
      have hfe : feasibleOn Θδ ω' Finset.univ = feasibleOn Θδ ω J := by
        ext θ; simp only [feasibleOn, Set.mem_setOf_eq, Finset.mem_univ, true_implies]
        constructor
        · intro h i hi; have := h i; simpa [hω', hi] using this
        · intro h i
          by_cases hi : i ∈ J
          · simpa [hω', hi] using h i hi
          · simpa [hω', hi] using h j0 hj0
      have hGω : G (fun i => ω i.1) = θstar ω' := by
        congr 1
      have heq : G (fun i => ω i.1) = θstar ω := by
        rw [hGω]
        exact h1'.2 _ ((vt_sol_congr f Θδ ω' ω _ J hfe _).1 (hθstar ω').1)
      rw [heq]; exact ⟨hc, fun i _ => (hθstar ω).1.1 i (Finset.mem_univ _)⟩
  have hsub : {ω | ε (alg ω).card < violation P Θδ (θstar ω)} ⊆
      ⋃ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
        {ω | alg ω = J ∧ ε J.card < violation P Θδ (θstar ω)} := by
    intro ω hω
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨alg ω, ?_, rfl, hω⟩
    have hle : (alg ω).card ≤ N := by
      simpa using Finset.card_le_univ (alg ω)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have := vt_viol_le_one P Θδ (θstar ω)
      simp only [Set.mem_setOf_eq, h, hεN] at hω
      linarith
  have hnn : ∀ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
      0 ≤ (1 - ε J.card) ^ (N - J.card) := by
    intro J hJ
    have := (hε J.card (Finset.mem_filter.1 hJ).2.le).2
    exact pow_nonneg (by linarith) _
  calc Measure.pi (fun _ : Fin N => P) {ω | ε (alg ω).card < violation P Θδ (θstar ω)}
      ≤ Measure.pi (fun _ : Fin N => P) (⋃ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
        {ω | alg ω = J ∧ ε J.card < violation P Θδ (θstar ω)}) := measure_mono hsub
    _ ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
          Measure.pi (fun _ : Fin N => P) {ω | alg ω = J ∧ ε J.card < violation P Θδ (θstar ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
          ENNReal.ofReal ((1 - ε J.card) ^ (N - J.card)) := Finset.sum_le_sum fun J _ => hEJ J
    _ = ENNReal.ofReal (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin N) => J.card < N),
          (1 - ε J.card) ^ (N - J.card)) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ = _ := by rw [vt_comb N (fun k => (1 - ε k) ^ (N - k))]

end ScenarioApproach.Nonconvex

open ScenarioApproach.Nonconvex


theorem solution {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (ε : ℕ → ℝ) (hε : ∀ k ≤ N, ε k ∈ Set.Icc (0 : ℝ) 1) (hεN : ε N = 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε (alg ω).card < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - ε k) ^ (N - k)) := by
  exact vt_core P f Θδ N hmeas θstar hθstar hθstar_meas alg halg ε hε hεN
