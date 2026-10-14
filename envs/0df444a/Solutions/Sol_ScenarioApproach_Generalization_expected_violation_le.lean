-- Prove2me | solution 1 for ScenarioApproach.Generalization.expected_violation_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:21:00.102396+00:00
-- url     : https://prove2.me/submissions/ac0f1026-336c-438b-9c69-421bc0c45402

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint



namespace ScenarioApproach.Generalization

open MeasureTheory

theorem ev_card_core {d m : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (hθstar : IsSolution c Θ Θδ ω θstar) :
    numSupportConstraints c Θ Θδ ω θstar ≤ d := by
  classical
  by_contra hlt
  push Not at hlt
  unfold numSupportConstraints at hlt
  set S := (Finset.univ.filter fun i : Fin m => IsSupportConstraint c Θ Θδ ω θstar i) with hS
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S) (n := d + 1) (by omega)
  let g : Fin (d + 1) → Fin m := fun j => ((T.equivFin.symm (Fin.cast hTcard.symm j)) : Fin m)
  have ginj : Function.Injective g := by
    intro a b hab
    have := Subtype.ext hab
    have := T.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  have gS : ∀ j, IsSupportConstraint c Θ Θδ ω θstar (g j) := by
    intro j
    have h1 : g j ∈ S := hTS (T.equivFin.symm (Fin.cast hTcard.symm j)).2
    rw [hS, Finset.mem_filter] at h1
    exact h1.2
  choose θ hθΘ hθδ hθc using gS
  let p : Option (Fin (d + 1)) → EuclideanSpace ℝ (Fin d) := fun o =>
    match o with
    | none => θstar
    | some j => θ j
  have hfeas := hθstar.1
  have hstarΘ : θstar ∈ Θ := hfeas.1
  have hstarδ : ∀ l, θstar ∈ Θδ (ω l) := by
    intro l; exact Set.mem_iInter.mp hfeas.2 l
  have hnot : ¬ AffineIndependent ℝ p := by
    intro hai
    have := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range p))
    rw [finrank_euclideanSpace_fin] at h2
    simp at this
    omega
  obtain ⟨I, q, hq1, hq2⟩ := Convex.radon_partition hnot
  have hpΘ : ∀ o, p o ∈ Θ := by
    intro o; cases o with
    | none => exact hstarΘ
    | some j => exact hθΘ j
  have hqΘ : q ∈ Θ := (convexHull_min (by rintro _ ⟨o, -, rfl⟩; exact hpΘ o) hΘ_convex) hq1
  have hqδ : ∀ l, q ∈ Θδ (ω l) := by
    intro l
    by_cases hA : ∃ j, some j ∈ I ∧ g j = l
    · obtain ⟨j, hjI, hjl⟩ := hA
      refine (convexHull_min ?_ (hΘδ_convex _)) hq2
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact hstarδ l
      | some j' =>
        apply hθδ j' l
        intro h
        rw [← hjl] at h
        have := ginj h
        subst this
        exact ho hjI
    · push Not at hA
      refine (convexHull_min ?_ (hΘδ_convex _)) hq1
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact hstarδ l
      | some j' =>
        apply hθδ j' l
        intro h
        exact hA j' ho h.symm
  have hqfeas : q ∈ feasibleSet Θ Θδ ω := ⟨hqΘ, Set.mem_iInter.mpr hqδ⟩
  have hle := hθstar.2 q hqfeas
  have hconv : Convex ℝ {x : EuclideanSpace ℝ (Fin d) | inner ℝ c x < inner ℝ c θstar} :=
    convex_halfSpace_lt (f := fun x => inner ℝ c x) (innerₛₗ ℝ c).isLinear _
  have hlt' : inner ℝ c q < inner ℝ c θstar := by
    by_cases hn : none ∈ I
    · refine (convexHull_min ?_ hconv) hq2
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact absurd hn ho
      | some j => exact hθc j
    · refine (convexHull_min ?_ hconv) hq1
      rintro _ ⟨o, ho, rfl⟩
      cases o with
      | none => exact absurd ho hn
      | some j => exact hθc j
  linarith

open Classical in
/-- pointwise: number of leave-one-out violators is at most `d`. -/
theorem ev_loo_card {d N : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (ω' : Fin (N + 1) → Δ) :
    (Finset.univ.filter fun k : Fin (N + 1) =>
        θstar (fun j => ω' (k.succAbove j)) ∉ Θδ (ω' k)).card ≤ d := by
  classical
  obtain ⟨θ', hθ', -⟩ := hexu (N + 1) ω'
  refine le_trans ?_ (ev_card_core c Θ Θδ hΘ_convex hΘδ_convex ω' θ' hθ')
  unfold numSupportConstraints
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  set ωk : Fin N → Δ := fun j => ω' (k.succAbove j) with hωk
  have hsk := hθstar ωk
  refine ⟨θstar ωk, hsk.1.1, ?_, ?_⟩
  · intro j hj
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact Set.mem_iInter.mp hsk.1.2 j'
  · have hθ'feas : θ' ∈ feasibleSet Θ Θδ ωk :=
      ⟨hθ'.1.1, Set.mem_iInter.mpr fun j => Set.mem_iInter.mp hθ'.1.2 (k.succAbove j)⟩
    have h1 := hsk.2 θ' hθ'feas
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      have hsol : IsSolution c Θ Θδ ωk θ' := by
        refine ⟨hθ'feas, fun x hx => ?_⟩
        rw [← h]; exact hsk.2 x hx
      obtain ⟨u, -, hu⟩ := hexu N ωk
      have e1 := hu _ hsol
      have e2 := hu _ hsk
      have : θ' = θstar ωk := e1.trans e2.symm
      exact hk (this ▸ Set.mem_iInter.mp hθ'.1.2 k)

theorem ev_core
    {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar) :
    MeasureTheory.Integrable (fun ω => violation P Θδ (θstar ω))
        (MeasureTheory.Measure.pi fun _ : Fin N => P) ∧
      ∫ ω, violation P Θδ (θstar ω) ∂(MeasureTheory.Measure.pi fun _ : Fin N => P) ≤
        (d : ℝ) / (N + 1) := by
  classical
  set μN := Measure.pi fun _ : Fin N => P with hμN
  set μN1 := Measure.pi fun _ : Fin (N + 1) => P with hμN1
  -- measurability
  have hC : MeasurableSet {q : (Fin N → Δ) × Δ | θstar q.1 ∉ Θδ q.2} := by
    have : {q : (Fin N → Δ) × Δ | θstar q.1 ∉ Θδ q.2} =
        (fun q : (Fin N → Δ) × Δ => (θstar q.1, q.2)) ⁻¹'
          {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2}ᶜ := rfl
    rw [this]
    exact ((hθstar_meas.comp measurable_fst).prodMk measurable_snd) hmeas.compl
  have hfm : Measurable fun ω : Fin N → Δ => P (violationSet Θδ (θstar ω)) :=
    measurable_measure_prodMk_left hC
  set L := ∫⁻ ω, P (violationSet Θδ (θstar ω)) ∂μN with hL
  have hB : MeasurableSet {q : Δ × (Fin N → Δ) | θstar q.2 ∉ Θδ q.1} := by
    have : {q : Δ × (Fin N → Δ) | θstar q.2 ∉ Θδ q.1} =
        (fun q : Δ × (Fin N → Δ) => (θstar q.2, q.1)) ⁻¹'
          {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2}ᶜ := rfl
    rw [this]
    exact ((hθstar_meas.comp measurable_snd).prodMk measurable_fst) hmeas.compl
  have hprod : (P.prod μN) {q : Δ × (Fin N → Δ) | θstar q.2 ∉ Θδ q.1} = L := by
    rw [Measure.prod_apply_symm hB]
    rfl
  let A : Fin (N + 1) → Set (Fin (N + 1) → Δ) := fun k =>
    {ω' | θstar (fun j => ω' (k.succAbove j)) ∉ Θδ (ω' k)}
  have hApre : ∀ k, A k = (MeasurableEquiv.piFinSuccAbove (fun _ => Δ) k) ⁻¹'
      {q : Δ × (Fin N → Δ) | θstar q.2 ∉ Θδ q.1} := by
    intro k; ext ω'; rfl
  have hAmeas : ∀ k, MeasurableSet (A k) := by
    intro k; rw [hApre k]; exact (MeasurableEquiv.measurable _) hB
  have hAk : ∀ k, μN1 (A k) = L := by
    intro k
    rw [hApre k, (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => P) k).measure_preimage
      hB.nullMeasurableSet]
    exact hprod
  have hsum : ((N : ENNReal) + 1) * L ≤ d := by
    have e1 : ((N : ENNReal) + 1) * L = ∑ k : Fin (N + 1), μN1 (A k) := by
      simp [hAk]
    rw [e1]
    have e2 : ∀ k, μN1 (A k) = ∫⁻ ω', (A k).indicator 1 ω' ∂μN1 := fun k =>
      (lintegral_indicator_one (hAmeas k)).symm
    simp_rw [e2]
    rw [← lintegral_finset_sum _ (fun k _ => measurable_one.indicator (hAmeas k))]
    calc ∫⁻ ω', ∑ k : Fin (N + 1), (A k).indicator 1 ω' ∂μN1
        ≤ ∫⁻ _ω', (d : ENNReal) ∂μN1 := by
          apply lintegral_mono
          intro ω'
          show ∑ k : Fin (N + 1), (A k).indicator (1 : (Fin (N + 1) → Δ) → ENNReal) ω' ≤ (d : ENNReal)
          have : ∑ k : Fin (N + 1), (A k).indicator (1 : (Fin (N + 1) → Δ) → ENNReal) ω' =
              ((Finset.univ.filter fun k : Fin (N + 1) =>
                θstar (fun j => ω' (k.succAbove j)) ∉ Θδ (ω' k)).card : ENNReal) := by
            simp only [Set.indicator_apply, Pi.one_apply]
            rw [Finset.sum_boole]
            rfl
          rw [this]
          exact_mod_cast ev_loo_card c Θ Θδ hΘ_convex hΘδ_convex hexu θstar hθstar ω'
      _ = d := by simp
  have hLfin : L ≠ ⊤ := by
    intro h; rw [h] at hsum; simp at hsum
  refine ⟨?_, ?_⟩
  · exact integrable_toReal_of_lintegral_ne_top hfm.aemeasurable hLfin
  · have hint : ∫ ω, violation P Θδ (θstar ω) ∂μN = L.toReal := by
      unfold violation
      rw [integral_toReal hfm.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
    rw [hint]
    have h2 : ((N : ℝ) + 1) * L.toReal ≤ d := by
      have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hLfin) (by simp)).mpr hsum
      simpa [ENNReal.toReal_mul, ENNReal.toReal_add] using this
    rw [le_div_iff₀ (by positivity)]
    linarith

end ScenarioApproach.Generalization

open ScenarioApproach.Generalization


theorem solution
    {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    -- Assumption 3.4 (convexity): `Θ` and every `Θ_δ` are convex and closed
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    -- Assumption 3.6 (existence and uniqueness), for every `m` and every sample
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    -- measurability, glossed over on p. 33: the constraint relation is jointly measurable
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    -- `θstar ω` is the solution of the scenario program with the `N` sampled constraints `ω`
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hd : 1 ≤ d) :
    MeasureTheory.Integrable (fun ω => violation P Θδ (θstar ω))
        (MeasureTheory.Measure.pi fun _ : Fin N => P) ∧
      ∫ ω, violation P Θδ (θstar ω) ∂(MeasureTheory.Measure.pi fun _ : Fin N => P) ≤
        (d : ℝ) / (N + 1) := by
  exact ev_core P c Θ Θδ hΘ_convex hΘδ_convex hexu hmeas θstar hθstar hθstar_meas
