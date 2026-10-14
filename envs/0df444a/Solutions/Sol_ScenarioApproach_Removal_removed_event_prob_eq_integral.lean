-- Prove2me | solution 1 for ScenarioApproach.Removal.removed_event_prob_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:44:58.258698+00:00
-- url     : https://prove2.me/submissions/b6f541d7-4844-49dd-a9e0-ff81bb4ee0ba

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory


namespace ScenarioApproach.Removal

lemma sw_feasible_eq {d N : ℕ} {Δ : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin N → Δ) (J : Finset (Fin N)) :
    feasibleSetWithout Θ Θδ ω J = feasibleSet Θ Θδ (fun j : Fin (Jᶜ).card => ω ((Jᶜ).equivFin.symm j).1) := by
  ext θ
  simp only [feasibleSetWithout, feasibleSet, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun j => h _ ?_⟩
    exact Finset.mem_compl.1 ((Jᶜ).equivFin.symm j).2
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun i hi => ?_⟩
    have hi' : i ∈ Jᶜ := by simpa using hi
    have := h ((Jᶜ).equivFin ⟨i, hi'⟩)
    simpa using this

lemma sw_unique {d N : ℕ} {Δ : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (hexu : ExistsUniqueSolution Θ Θδ c)
    (ω : Fin N → Δ) (J : Finset (Fin N)) (θ1 θ2 : EuclideanSpace ℝ (Fin d))
    (h1 : IsSolutionWithout Θ Θδ c ω J θ1) (h2 : IsSolutionWithout Θ Θδ c ω J θ2) : θ1 = θ2 := by
  have hf := sw_feasible_eq Θ Θδ ω J
  unfold IsSolutionWithout at h1 h2
  rw [hf] at h1 h2
  exact (hexu _ _).unique h1 h2

lemma re_meas_viol {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2}) :
    Measurable (fun θ => ScenarioApproach.Generalization.violation P Θδ θ) := by
  unfold ScenarioApproach.Generalization.violation ScenarioApproach.Generalization.violationSet
  have := measurable_measure_prodMk_left (ν := P) hmeas.compl
  exact this.ennreal_toReal

lemma re_viol_le_one {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P] (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (θ) :
    ScenarioApproach.Generalization.violation P Θδ θ ≤ 1 := by
  unfold ScenarioApproach.Generalization.violation
  have := ENNReal.toReal_mono ENNReal.one_ne_top
    (prob_le_one (μ := P) (s := ScenarioApproach.Generalization.violationSet Θδ θ))
  simpa using this

lemma re_viol_nonneg {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (θ) :
    0 ≤ ScenarioApproach.Generalization.violation P Θδ θ := ENNReal.toReal_nonneg

lemma re_pi_pi {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (s : Set Δ) :
    Measure.pi (fun _ : ι => P) (Set.pi Set.univ fun _ => s) = P s ^ Fintype.card ι := by
  rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ]

theorem removed_event_prob_eq_integral_core {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (J : Finset (Fin N)) (hJ : J.card = k)
    (θJ : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθJ : ∀ ω, IsSolutionWithout Θ Θδ c ω J (θJ ω))
    (hθJ_meas : Measurable θJ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P)
        {ω | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θJ ω)} =
      ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k)
        ∂(Measure.map (fun ω => ScenarioApproach.Generalization.violation P Θδ (θJ ω)) (Measure.pi (fun _ : Fin N => P))) := by
  classical
  set V := fun θ => ScenarioApproach.Generalization.violation P Θδ θ with hVdef
  have hV : Measurable V := re_meas_viol P Θδ hmeas
  set μ := Measure.pi (fun _ : Fin N => P) with hμ
  set S := {ω : Fin N → Δ | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < V (θJ ω)} with hSdef
  have hS : MeasurableSet S := by
    have : S = (⋂ i ∈ J, {ω : Fin N → Δ | (θJ ω, ω i) ∈ {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2}ᶜ})
        ∩ {ω | ε < V (θJ ω)} := by
      ext ω; simp [S]
    rw [this]
    refine MeasurableSet.inter (Finset.measurableSet_biInter _ fun i _ => ?_) ?_
    · exact hmeas.compl.preimage (hθJ_meas.prodMk (measurable_pi_apply i))
    · exact measurableSet_lt measurable_const (hV.comp hθJ_meas)
  set F : EuclideanSpace ℝ (Fin d) → ENNReal :=
    fun θ => (Set.Ioc ε 1).indicator (fun α : ℝ => ENNReal.ofReal (α ^ k)) (V θ) with hFdef
  have hFm : Measurable (fun α : ℝ => (Set.Ioc ε 1).indicator (fun α : ℝ => ENNReal.ofReal (α ^ k)) α) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const k)).indicator measurableSet_Ioc
  have hF : Measurable F := hFm.comp hV
  -- RHS as integral over μ
  have hR : ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k) ∂(Measure.map (fun ω => V (θJ ω)) μ)
      = ∫⁻ ω, F (θJ ω) ∂μ := by
    rw [← lintegral_indicator measurableSet_Ioc,
      lintegral_map (g := fun ω => V (θJ ω)) hFm (hV.comp hθJ_meas : Measurable fun ω => V (θJ ω))]
  have hR' : ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k)
        ∂(Measure.map (fun ω => ScenarioApproach.Generalization.violation P Θδ (θJ ω)) μ)
      = ∫⁻ ω, F (θJ ω) ∂μ := hR
  rw [hR']
  rw [← lintegral_indicator_one hS]
  -- split
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => Δ) (fun i => i ∈ J) with he
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => P) (fun i => i ∈ J)
  have hmps := hmp.symm e
  rw [← hmps.lintegral_comp_emb e.symm.measurableEmbedding,
    ← hmps.lintegral_comp_emb e.symm.measurableEmbedding]
  rw [lintegral_prod_symm (fun p => S.indicator (1 : (Fin N → Δ) → ENNReal) (e.symm p))
      (((measurable_const.indicator hS).comp e.symm.measurable).aemeasurable),
    lintegral_prod_symm (fun p => F (θJ (e.symm p)))
      ((hF.comp (hθJ_meas.comp e.symm.measurable)).aemeasurable)]
  apply lintegral_congr
  intro y
  haveI : Nonempty Δ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨x0⟩ : Nonempty ((i : {i // i ∈ J}) → Δ) := inferInstance
  set θ0 := θJ (e.symm (x0, y)) with hθ0
  have hconst : ∀ x, θJ (e.symm (x, y)) = θ0 := by
    intro x
    apply sw_unique Θ Θδ c hexu (e.symm (x, y)) J _ _ (hθJ _)
    have hfe : feasibleSetWithout Θ Θδ (e.symm (x, y)) J = feasibleSetWithout Θ Θδ (e.symm (x0, y)) J := by
      ext θ
      simp only [feasibleSetWithout, Set.mem_inter_iff, Set.mem_iInter]
      have : ∀ i, i ∉ J → e.symm (x, y) i = e.symm (x0, y) i := by
        intro i hi
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
      constructor
      · rintro ⟨h0, h⟩; exact ⟨h0, fun i hi => by rw [← this i hi]; exact h i hi⟩
      · rintro ⟨h0, h⟩; exact ⟨h0, fun i hi => by rw [this i hi]; exact h i hi⟩
    unfold IsSolutionWithout; rw [hfe]; exact hθJ _
  simp only [hconst]
  rw [lintegral_const, measure_univ, mul_one]
  have hval : ∀ x, e.symm (x, y) ∈ S ↔ (∀ i : {i // i ∈ J}, x i ∈ ScenarioApproach.Generalization.violationSet Θδ θ0) ∧ ε < V θ0 := by
    intro x
    simp only [S, Set.mem_setOf_eq, hconst, ScenarioApproach.Generalization.violationSet]
    have hx : ∀ i (hi : i ∈ J), e.symm (x, y) i = x ⟨i, hi⟩ := by
      intro i hi
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by have := h1 i.1 i.2; rw [hx i.1 i.2] at this; exact this, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i hi => by rw [hx i hi]; exact h1 ⟨i, hi⟩, h2⟩
  have hvs : MeasurableSet (ScenarioApproach.Generalization.violationSet Θδ θ0) :=
    (measurable_prodMk_left (β := Δ) (x := θ0)) hmeas.compl
  by_cases hε : ε < V θ0
  · have hfun : (fun x => S.indicator (1 : (Fin N → Δ) → ENNReal) (e.symm (x, y))) =
        (Set.pi Set.univ (fun _ => ScenarioApproach.Generalization.violationSet Θδ θ0)).indicator 1 := by
      funext x
      by_cases hx : e.symm (x, y) ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        · rfl
        · intro i _; exact ((hval x).1 hx).1 i
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        intro h; apply hx; exact (hval x).2 ⟨fun i => h i (Set.mem_univ _), hε⟩
    rw [hfun, lintegral_indicator_one (MeasurableSet.univ_pi fun _ => hvs), re_pi_pi,
      Fintype.card_coe, hJ]
    have hle := re_viol_le_one P Θδ θ0
    have h0 := re_viol_nonneg P Θδ θ0
    simp only [F]
    rw [Set.indicator_of_mem (show V θ0 ∈ Set.Ioc ε 1 from ⟨hε, hle⟩), ENNReal.ofReal_pow h0]
    congr 1
    simp only [ScenarioApproach.Generalization.violation]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · have hfun : (fun x => S.indicator (1 : (Fin N → Δ) → ENNReal) (e.symm (x, y))) = fun _ => 0 := by
      funext x
      rw [Set.indicator_of_notMem]
      intro hx; exact hε ((hval x).1 hx).2
    rw [hfun, lintegral_zero]
    simp only [F]
    rw [Set.indicator_of_notMem]
    intro h; exact hε h.1

end ScenarioApproach.Removal

open ScenarioApproach.Removal


theorem solution {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (J : Finset (Fin N)) (hJ : J.card = k)
    (θJ : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθJ : ∀ ω, IsSolutionWithout Θ Θδ c ω J (θJ ω))
    (hθJ_meas : Measurable θJ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P)
        {ω | (∀ i ∈ J, θJ ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θJ ω)} =
      ∫⁻ α in Set.Ioc ε 1, ENNReal.ofReal (α ^ k)
        ∂(Measure.map (fun ω => ScenarioApproach.Generalization.violation P Θδ (θJ ω)) (Measure.pi (fun _ : Fin N => P))) := by
  exact removed_event_prob_eq_integral_core P Θ Θδ c hexu hmeas J hJ θJ hθJ hθJ_meas ε hε0 hε1
