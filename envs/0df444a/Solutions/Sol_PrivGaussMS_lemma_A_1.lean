-- Prove2me | solution 1 for PrivGaussMS.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:35:22.814833+00:00
-- url     : https://prove2.me/submissions/56833781-b2b7-45b0-97c7-0bb2261b5c41

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory

namespace SolPrivGaussMSA1

lemma tv_bdd {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    BddAbove (Set.range fun s : {s : Set α // MeasurableSet s} =>
      |(μ s.1).toReal - (ν s.1).toReal|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨s, rfl⟩
  have a1 : (μ s.1).toReal ≤ 1 := measureReal_le_one
  have a2 : (ν s.1).toReal ≤ 1 := measureReal_le_one
  have a3 : 0 ≤ (μ s.1).toReal := ENNReal.toReal_nonneg
  have a4 : 0 ≤ (ν s.1).toReal := ENNReal.toReal_nonneg
  show |(μ s.1).toReal - (ν s.1).toReal| ≤ 1
  rw [abs_le]; constructor <;> linarith

lemma tv_ge {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set α) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ FoundationsRL.DECLower.tvDist μ ν :=
  le_ciSup (tv_bdd μ ν) ⟨A, hA⟩

lemma ennreal_of_real_ineq {Y : Type*} [MeasurableSpace Y] (μ μ' : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (ε δ : ℝ) (hδ : 0 ≤ δ) {O : Set Y}
    (h : μ.real O ≤ Real.exp ε * μ'.real O + δ) :
    μ O ≤ ENNReal.ofReal (Real.exp ε) * μ' O + ENNReal.ofReal δ := by
  have := ENNReal.ofReal_le_ofReal h
  rwa [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos ε).le measureReal_nonneg) hδ,
    ENNReal.ofReal_mul (Real.exp_pos ε).le, measureReal_def, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    at this

lemma real_of_ennreal_ineq {a b : ENNReal} (e δ : ℝ) (he : 0 ≤ e) (hδ : 0 ≤ δ) (hb : b ≠ ⊤)
    (h : a ≤ ENNReal.ofReal e * b + ENNReal.ofReal δ) :
    a.toReal ≤ e * b.toReal + δ := by
  have hne : ENNReal.ofReal e * b + ENNReal.ofReal δ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb, ENNReal.ofReal_ne_top⟩
  have h4 := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal he, ENNReal.toReal_ofReal hδ] at h4

lemma dp_fun {Y : Type*} [MeasurableSpace Y] (μ μ' : Measure Y)
    (c d : ENNReal) (hE : ∀ O, MeasurableSet O → μ O ≤ c * μ' O + d)
    (f : Y → ENNReal) (hf : Measurable f) (hf1 : ∀ y, f y ≤ 1) :
    ∫⁻ y, f y ∂μ ≤ c * ∫⁻ y, f y ∂μ' + d := by
  set g : Y → ℝ := fun y => (f y).toReal with hg_def
  have hg : Measurable g := hf.ennreal_toReal
  have hfg : ∀ y, f y = ENNReal.ofReal (g y) := fun y =>
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 y))).symm
  have hg1 : ∀ y, g y ≤ 1 := fun y => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 y)
    simpa [hg_def] using this
  have hg0 : ∀ y, 0 ≤ g y := fun y => ENNReal.toReal_nonneg
  have layer : ∀ ν : Measure Y, ∫⁻ y, f y ∂ν = ∫⁻ t in Set.Ioi 0, ν {a | t < g a} := by
    intro ν
    simp_rw [hfg]
    exact lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hg0) hg.aemeasurable
  rw [layer μ, layer μ']
  have hmeas0 : Measurable fun t : ℝ => μ' {a | t < g a} := by
    apply Antitone.measurable
    intro s t hst
    exact measure_mono fun a (ha : t < g a) => lt_of_le_of_lt hst ha
  have hmeas : Measurable fun t : ℝ => c * μ' {a | t < g a} := hmeas0.const_mul c
  calc ∫⁻ t in Set.Ioi 0, μ {a | t < g a}
      ≤ ∫⁻ t in Set.Ioi 0, (c * μ' {a | t < g a} + (Set.Iic (1 : ℝ)).indicator (fun _ => d) t) := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ≤ 1
        · rw [Set.indicator_of_mem (Set.mem_Iic.2 ht)]
          exact hE _ (measurableSet_lt measurable_const hg)
        · have : {a | t < g a} = ∅ := by
            ext a
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            linarith [hg1 a, not_le.1 ht]
          rw [this, measure_empty]
          exact zero_le
    _ = c * (∫⁻ t in Set.Ioi 0, μ' {a | t < g a}) +
          ∫⁻ t in Set.Ioi 0, (Set.Iic (1 : ℝ)).indicator (fun _ => d) t := by
        rw [lintegral_add_left hmeas, lintegral_const_mul _ hmeas0]
    _ = c * (∫⁻ t in Set.Ioi 0, μ' {a | t < g a}) + d := by
        rw [lintegral_indicator_const measurableSet_Iic d,
          Measure.restrict_apply measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic,
          Real.volume_Ioc]
        simp

/-- One direction of the coupling inequality, in `ℝ≥0∞`. -/
lemma coupling_le {α : Type*} [MeasurableSpace α] (γ : Measure (α × α)) (A : Set α)
    (hA : MeasurableSet A) :
    γ.map Prod.fst A ≤ γ.map Prod.snd A + γ {p | p.1 ≠ p.2} := by
  rw [Measure.map_apply measurable_fst hA, Measure.map_apply measurable_snd hA]
  calc γ (Prod.fst ⁻¹' A) ≤ γ (Prod.snd ⁻¹' A ∪ {p | p.1 ≠ p.2}) := by
        refine measure_mono fun p hp => ?_
        by_cases h : p.1 = p.2
        · left; show p.2 ∈ A; rw [← h]; exact hp
        · right; exact h
    _ ≤ _ := measure_union_le _ _

end SolPrivGaussMSA1

open SolPrivGaussMSA1 in
theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (hdiag : MeasurableSet (Set.diagonal α))
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (∀ γ : Measure (α × α), γ.map Prod.fst = P → γ.map Prod.snd = Q →
        FoundationsRL.DECLower.tvDist P Q ≤ γ.real {p | p.1 ≠ p.2}) ∧
    (∃ γ : Measure (α × α), γ.map Prod.fst = P ∧ γ.map Prod.snd = Q ∧
        FoundationsRL.DECLower.tvDist P Q = γ.real {p | p.1 ≠ p.2}) ∧
    (∀ K : Kernel α β, IsMarkovKernel K →
        FoundationsRL.DECLower.tvDist (P.bind K) (Q.bind K) ≤
          FoundationsRL.DECLower.tvDist P Q) := by
  haveI hne : Nonempty {s : Set α // MeasurableSet s} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  have hD : MeasurableSet {p : α × α | p.1 ≠ p.2} := hdiag.compl
  -- Part 1
  have part1 : ∀ γ : Measure (α × α), γ.map Prod.fst = P → γ.map Prod.snd = Q →
      FoundationsRL.DECLower.tvDist P Q ≤ γ.real {p | p.1 ≠ p.2} := by
    intro γ h1 h2
    haveI : IsFiniteMeasure γ := by
      constructor
      have : γ Set.univ = γ.map Prod.fst Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      rw [this, h1, measure_univ]
      exact ENNReal.one_lt_top
    refine ciSup_le fun s => ?_
    have e1 := coupling_le γ s.1 s.2
    have e2 := coupling_le (γ.map Prod.swap) s.1 s.2
    rw [h1, h2] at e1
    rw [Measure.map_map measurable_fst measurable_swap,
      Measure.map_map measurable_snd measurable_swap,
      Measure.map_apply measurable_swap hD] at e2
    have hfs : Prod.fst ∘ (Prod.swap : α × α → α × α) = Prod.snd := rfl
    have hss : Prod.snd ∘ (Prod.swap : α × α → α × α) = Prod.fst := rfl
    have hpre : (Prod.swap : α × α → α × α) ⁻¹' {p | p.1 ≠ p.2} = {p | p.1 ≠ p.2} := by
      ext p; simp [Prod.swap, ne_comm]
    rw [hfs, hss, h1, h2, hpre] at e2
    have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) e1
    have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) e2
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at r1 r2
    show |(P s.1).toReal - (Q s.1).toReal| ≤ (γ {p | p.1 ≠ p.2}).toReal
    rw [abs_le]; constructor <;> linarith
  refine ⟨part1, ?_, ?_⟩
  · obtain ⟨H, hH, hle1, hle2⟩ := hahn_decomposition P Q
    have hQP : Q.restrict H ≤ P.restrict H := by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
      exact hle1 _ (hs.inter hH) Set.inter_subset_right
    have hPQ : P.restrict Hᶜ ≤ Q.restrict Hᶜ := by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
      exact hle2 _ (hs.inter hH.compl) Set.inter_subset_right
    set a := P.restrict H - Q.restrict H with ha_def
    set b := Q.restrict Hᶜ - P.restrict Hᶜ with hb_def
    set m := Q.restrict H + P.restrict Hᶜ with hm_def
    have haP : a + m = P := by
      rw [hm_def, ← add_assoc, ha_def, Measure.sub_add_cancel_of_le hQP,
        Measure.restrict_add_restrict_compl hH]
    have hbQ : b + m = Q := by
      rw [hm_def, add_comm (Q.restrict H), ← add_assoc, hb_def,
        Measure.sub_add_cancel_of_le hPQ, add_comm, Measure.restrict_add_restrict_compl hH]
    haveI : IsFiniteMeasure a := by
      constructor
      have : a Set.univ ≤ P Set.univ := by
        rw [← haP]; simp
      exact lt_of_le_of_lt this (measure_lt_top _ _)
    haveI : IsFiniteMeasure b := by
      constructor
      have : b Set.univ ≤ Q Set.univ := by
        rw [← hbQ]; simp
      exact lt_of_le_of_lt this (measure_lt_top _ _)
    haveI : IsFiniteMeasure m := by
      constructor
      have : m Set.univ ≤ P Set.univ := by
        rw [← haP]; simp
      exact lt_of_le_of_lt this (measure_lt_top _ _)
    set τ := a Set.univ with hτ_def
    have hτb : b Set.univ = τ := by
      have h1 : a Set.univ + m Set.univ = b Set.univ + m Set.univ := by
        rw [← Measure.add_apply, ← Measure.add_apply, haP, hbQ, measure_univ, measure_univ]
      exact ((ENNReal.add_left_inj (measure_ne_top m _)).1 h1).symm
    have hτtop : τ ≠ ⊤ := measure_ne_top _ _
    have haHc : a Hᶜ = 0 := by
      rw [ha_def, Measure.sub_apply hH.compl hQP, Measure.restrict_apply hH.compl,
        Measure.restrict_apply hH.compl]
      simp
    have hbH : b H = 0 := by
      rw [hb_def, Measure.sub_apply hH hPQ, Measure.restrict_apply hH,
        Measure.restrict_apply hH]
      simp
    have haH : a H = τ := by
      have := measure_add_measure_compl (μ := a) hH
      rw [haHc, add_zero] at this
      exact this
    have hbHc : b Hᶜ = τ := by
      have := measure_add_measure_compl (μ := b) hH
      rw [hbH, zero_add] at this
      rw [this, hτb]
    have hcancel : ∀ ν : Measure α, ν Set.univ = 0 ∨ τ ≠ 0 → τ⁻¹ • τ • ν = ν := by
      intro ν hν
      rcases eq_or_ne τ 0 with h0 | h0
      · rcases hν with hν | hν
        · rw [Measure.measure_univ_eq_zero.1 hν]; simp
        · exact absurd h0 hν
      · rw [smul_smul, ENNReal.inv_mul_cancel h0 hτtop, one_smul]
    have hτ0a : a Set.univ = 0 ∨ τ ≠ 0 := by
      rcases eq_or_ne τ 0 with h0 | h0
      · left; exact h0
      · right; exact h0
    have hτ0b : b Set.univ = 0 ∨ τ ≠ 0 := by
      rcases eq_or_ne τ 0 with h0 | h0
      · left; rw [hτb]; exact h0
      · right; exact h0
    have hdm : Measurable fun x : α => (x, x) := measurable_id.prodMk measurable_id
    refine ⟨m.map (fun x => (x, x)) + τ⁻¹ • (a.prod b), ?_, ?_, ?_⟩
    · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_fst_prod,
        Measure.map_map measurable_fst hdm, hτb]
      have : (Prod.fst ∘ fun x : α => (x, x)) = id := rfl
      rw [this, Measure.map_id, hcancel a hτ0a, add_comm, haP]
    · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_snd_prod,
        Measure.map_map measurable_snd hdm]
      have : (Prod.snd ∘ fun x : α => (x, x)) = id := rfl
      rw [this, Measure.map_id, ← hτ_def, hcancel b hτ0b, add_comm, hbQ]
    · have hprod : (a.prod b) {p : α × α | p.1 ≠ p.2} = τ * τ := by
        apply le_antisymm
        · calc (a.prod b) {p : α × α | p.1 ≠ p.2} ≤ (a.prod b) Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = τ * τ := by
                rw [← Set.univ_prod_univ, Measure.prod_prod, hτb]
        · calc τ * τ = (a.prod b) (H ×ˢ Hᶜ) := by rw [Measure.prod_prod, haH, hbHc]
            _ ≤ _ := by
                refine measure_mono fun p hp => ?_
                obtain ⟨h1, h2⟩ := hp
                intro heq
                exact h2 (heq ▸ h1)
      have hγ : (m.map (fun x => (x, x)) + τ⁻¹ • (a.prod b)) {p : α × α | p.1 ≠ p.2} = τ := by
        rw [Measure.add_apply, Measure.smul_apply, Measure.map_apply hdm hD, hprod, smul_eq_mul]
        have : (fun x : α => (x, x)) ⁻¹' {p : α × α | p.1 ≠ p.2} = ∅ := by
          ext x; simp
        rw [this, measure_empty, zero_add]
        rcases eq_or_ne τ 0 with h0 | h0
        · rw [h0, mul_zero, mul_zero]
        · rw [← mul_assoc, ENNReal.inv_mul_cancel h0 hτtop, one_mul]
      have hmarg1 : (m.map (fun x => (x, x)) + τ⁻¹ • (a.prod b)).map Prod.fst = P := by
        rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_fst_prod,
          Measure.map_map measurable_fst hdm, hτb]
        have : (Prod.fst ∘ fun x : α => (x, x)) = id := rfl
        rw [this, Measure.map_id, hcancel a hτ0a, add_comm, haP]
      have hmarg2 : (m.map (fun x => (x, x)) + τ⁻¹ • (a.prod b)).map Prod.snd = Q := by
        rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_snd_prod,
          Measure.map_map measurable_snd hdm]
        have : (Prod.snd ∘ fun x : α => (x, x)) = id := rfl
        rw [this, Measure.map_id, ← hτ_def, hcancel b hτ0b, add_comm, hbQ]
      apply le_antisymm (part1 _ hmarg1 hmarg2)
      rw [measureReal_def, hγ]
      refine le_trans ?_ (tv_ge P Q H hH)
      have hPH : P H = a H + Q H := by
        have := congrArg (fun ν : Measure α => ν H) haP
        simp only [Measure.add_apply] at this
        rw [← this, hm_def, Measure.add_apply, Measure.restrict_apply hH,
          Measure.restrict_apply hH, Set.inter_self, Set.inter_compl_self, measure_empty,
          add_zero]
      rw [← haH]
      have : (a H).toReal = P.real H - Q.real H := by
        rw [measureReal_def, measureReal_def, hPH,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        ring
      rw [this]
      exact le_abs_self _
  · intro K hK
    have hb : ∀ μ : Measure α, IsProbabilityMeasure μ → IsProbabilityMeasure (μ.bind K) :=
      fun μ hμ => by
        constructor
        rw [Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
        simp
    haveI := hb P inferInstance
    haveI := hb Q inferInstance
    set T := FoundationsRL.DECLower.tvDist P Q
    have hT : 0 ≤ T := le_trans (abs_nonneg _) (tv_ge P Q ∅ MeasurableSet.empty)
    have dir : ∀ (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∀ A, MeasurableSet A → μ.real A - ν.real A ≤ T) →
        ∀ E, MeasurableSet E → ((μ.bind K) E).toReal ≤ ((ν.bind K) E).toReal + T := by
      intro μ ν _ _ hμν E hE
      have hE' : ∀ O, MeasurableSet O →
          μ O ≤ ENNReal.ofReal (Real.exp 0) * ν O + ENNReal.ofReal T := fun O hO =>
        ennreal_of_real_ineq μ ν 0 T hT (by rw [Real.exp_zero, one_mul]; linarith [hμν O hO])
      have key : μ.bind K E ≤ ENNReal.ofReal (Real.exp 0) * ν.bind K E + ENNReal.ofReal T := by
        rw [Measure.bind_apply hE K.measurable.aemeasurable,
          Measure.bind_apply hE K.measurable.aemeasurable]
        exact dp_fun μ ν _ _ hE' (fun y => K y E) (K.measurable_coe hE)
          (fun y => prob_le_one)
      have := real_of_ennreal_ineq _ _ (Real.exp_pos 0).le hT (measure_ne_top _ _) key
      rwa [Real.exp_zero, one_mul] at this
    have d1 := dir P Q (fun A hA => le_trans (le_abs_self _) (tv_ge P Q A hA))
    have d2 := dir Q P (fun A hA => by
      have := tv_ge P Q A hA
      rw [abs_le] at this
      linarith [this.1])
    refine ciSup_le fun s => ?_
    have e1 := d1 s.1 s.2
    have e2 := d2 s.1 s.2
    show |((P.bind K) s.1).toReal - ((Q.bind K) s.1).toReal| ≤ T
    rw [abs_le]; constructor <;> linarith
