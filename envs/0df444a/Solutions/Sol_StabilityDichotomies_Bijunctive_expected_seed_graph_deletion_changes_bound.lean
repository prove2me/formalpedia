-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.expected_seed_graph_deletion_changes_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:27:45.533074+00:00
-- url     : https://prove2.me/submissions/87583076-c95d-45ad-b400-6c3d87241d22

import Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deletion_change_count_le_maximum_shift
import Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deleted_bit_event_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_predicate_event_measurable
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_exponential_expected_maximum_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_exponential_positive_ae
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem thinned_member {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V)
    (hc : c ∈ (thinnedInstance I mask).constraints) : c ∈ I.constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn] at hc
  obtain ⟨⟨i,d⟩,⟨⟨j,hj⟩,hm⟩,hd⟩ := hc
  cases hj
  simp only [Prod.snd] at hd
  subst c
  simp only [occurrenceAt]
  exact Multiset.mem_toList.mp (List.get_mem _ _)

theorem solution {Γ : Language} {V : Type} [Fintype V] [Nonempty V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (ε : ℝ) (hε : 0 < ε) (v : V) :
    let μ := bijunctiveSeedMeasure rep I ε
    let C := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      ∑ j : Fin I.constraints.card,
        if decide (literalScore rep
          (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
          (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)) ≠
          bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v then (1 : ℝ) else 0
    Integrable C μ ∧ (∫ s, C s ∂μ) ≤
      (Real.log (Fintype.card (Literal V)) + 1) / bijunctiveRate rep ε := by
  classical
  letI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hβ : 0 < bijunctiveRate rep ε := by
    unfold bijunctiveRate
    apply div_pos hε
    have hh : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  letI : IsProbabilityMeasure (expMeasure (bijunctiveRate rep ε)) := isProbabilityMeasure_expMeasure hβ
  letI : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := isProbabilityMeasure_expMeasure hβ
  let μP : Measure (Fin I.constraints.card → ℝ) := Measure.pi (fun _ => unitPriorityMeasure)
  let μD : Measure (Literal V → ℝ) := Measure.pi (fun _ => shiftMeasure (bijunctiveRate rep ε))
  let μC := cutoffMeasure ε
  haveI : IsProbabilityMeasure μP := by unfold μP; infer_instance
  haveI : IsProbabilityMeasure μD := by unfold μD; infer_instance
  haveI : IsProbabilityMeasure μC := by unfold μC; infer_instance
  let μ := μP.prod (μC.prod μD)
  let bit := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
    bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v
  let bitdel := fun (j : Fin I.constraints.card) (s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
    decide (literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true))
  let C := fun s => ∑ j : Fin I.constraints.card, if bitdel j s ≠ bit s then (1 : ℝ) else 0
  let M : (Literal V → ℝ) → ℝ := fun δ => max 0 (Finset.univ.sup' Finset.univ_nonempty δ)
  let proj := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) => s.2.2
  have hP : MeasurePreserving proj μ μD := by
    have houter : MeasurePreserving Prod.snd (μP.prod (μC.prod μD)) (μC.prod μD) := measurePreserving_snd
    have hinner : MeasurePreserving Prod.snd (μC.prod μD) μD := measurePreserving_snd
    exact hinner.comp houter
  have hbit : MeasurableSet {s | bit s = true} :=
    bijunctive_output_predicate_event_measurable rep I ε (fun x => x v = true)
  have hdel (j : Fin I.constraints.card) : MeasurableSet {s | bitdel j s = true} := by
    simpa [bitdel] using graph_deleted_bit_event_measurable rep I ε j v
  have hchange (j : Fin I.constraints.card) : MeasurableSet {s | bitdel j s ≠ bit s} := by
    have hs : {s | bitdel j s ≠ bit s} =
      ({s | bitdel j s = true} ∩ {s | bit s = true}ᶜ) ∪
      ({s | bitdel j s = true}ᶜ ∩ {s | bit s = true}) := by
      ext s
      cases h1 : bitdel j s <;> cases h2 : bit s <;> simp [h1,h2]
    rw [hs]
    exact ((hdel j).inter hbit.compl).union ((hdel j).compl.inter hbit)
  have hCm : Measurable C := by
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (hchange j) measurable_const measurable_const
  have hC0 (s) : 0 ≤ C s := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num
  have hM := finite_exponential_expected_maximum_bound (α := Literal V) (bijunctiveRate rep ε) hβ
  have hM' : Integrable (M ∘ proj) μ := (hP.integrable_comp hM.1.aestronglyMeasurable).2 hM.1
  have hpos : ∀ᵐ s ∂μ, ∀ a, 0 < proj s a :=
    hP.quasiMeasurePreserving.ae (finite_independent_exponential_positive_ae (α := Literal V) (bijunctiveRate rep ε) hβ)
  have hbound : ∀ᵐ s ∂μ, C s ≤ (M ∘ proj) s := by
    filter_upwards [hpos] with s hs
    let F := thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))
    let mask := fun i => decide (s.1 i ≤ 1 - ε / 2)
    have hF : Satisfiable F := by
      obtain ⟨x,hx⟩ := hI
      exact ⟨x,fun c hc => hx c (thinned_member I _ c hc)⟩
    have hc := graph_deletion_change_count_le_maximum_shift rep I F hF mask s.2.2 hs v
    change (∑ j : Fin I.constraints.card, if bitdel j s ≠ bit s then (1 : ℝ) else 0) ≤ M s.2.2
    rw [Finset.sum_boole]
    exact hc
  have hCi : Integrable C μ := by
    apply hM'.mono' hCm.aestronglyMeasurable
    filter_upwards [hbound] with s hs
    rwa [Real.norm_eq_abs,abs_of_nonneg (hC0 s)]
  have heq : (∫ s, (M ∘ proj) s ∂μ) = ∫ δ, M δ ∂μD := by
    have hm : AEStronglyMeasurable M (Measure.map proj μ) := by rw [hP.map_eq]; exact hM.1.aestronglyMeasurable
    have h := integral_map hP.measurable.aemeasurable hm
    rw [hP.map_eq] at h
    exact h.symm
  have hh := integral_mono_ae hCi hM' hbound
  rw [heq] at hh
  exact ⟨hCi,hh.trans hM.2⟩
