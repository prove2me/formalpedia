-- Prove2me | solution 1 for StabilityDichotomies.Solvability.wasserstein_le_measurable_seed_bit_changes
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:43:14.868197+00:00
-- url     : https://prove2.me/submissions/de2858f3-a0e7-4010-bb1c-0a201cbe42e9

import Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_shared_seed_cost
noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability

theorem wasserstein_le_measurable_seed_joint_cost {V Ω : Type} [Fintype V] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → V → Bool)
    (hf : Measurable f) (hg : Measurable g) :
    letI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
    letI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
    wasserstein ((Measure.map f μ).toPMF) ((Measure.map g μ).toPMF) ≤
      ∑ x : V → Bool, ∑ y : V → Bool,
        (μ {ω | f ω = x ∧ g ω = y}).toReal * hammingCost x y := by
  classical
  let h : Ω → (V → Bool) × (V → Bool) := fun ω => (f ω, g ω)
  have hh : Measurable h := hf.prodMk hg
  haveI : IsProbabilityMeasure (Measure.map h μ) := Measure.isProbabilityMeasure_map hh.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
  let ρ : PMF ((V → Bool) × (V → Bool)) := (Measure.map h μ).toPMF
  have hfst : ρ.map Prod.fst = (Measure.map f μ).toPMF := by
    apply PMF.toMeasure_inj.mp
    rw [← PMF.toMeasure_map _ _ measurable_fst, Measure.toPMF_toMeasure, Measure.toPMF_toMeasure,
      Measure.map_map measurable_fst hh]
    rfl
  have hsnd : ρ.map Prod.snd = (Measure.map g μ).toPMF := by
    apply PMF.toMeasure_inj.mp
    rw [← PMF.toMeasure_map _ _ measurable_snd, Measure.toPMF_toMeasure, Measure.toPMF_toMeasure,
      Measure.map_map measurable_snd hh]
    rfl
  have hb := wasserstein_le_shared_seed_cost ρ Prod.fst Prod.snd
  rw [hfst,hsnd] at hb
  refine hb.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  have he : ρ (x,y) = μ {ω | f ω = x ∧ g ω = y} := by
    change (Measure.map h μ).toPMF (x,y) = _
    rw [Measure.toPMF_apply, Measure.map_apply hh (measurableSet_singleton _)]
    congr 1
    ext ω
    simp [h]
  rw [he]

theorem solution {V Ω : Type} [Fintype V] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → V → Bool)
    (hf : Measurable f) (hg : Measurable g) :
    letI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
    letI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
    wasserstein ((Measure.map f μ).toPMF) ((Measure.map g μ).toPMF) ≤
      ∑ v : V, (μ {ω | f ω v ≠ g ω v}).toReal := by
  classical
  have h := wasserstein_le_measurable_seed_joint_cost μ f g hf hg
  refine h.trans ?_
  have hh (x y : V → Bool) : hammingCost x y = ∑ v : V, if x v ≠ y v then (1 : ℝ) else 0 := by
    unfold hammingCost
    rw [hammingDist, ← Finset.sum_boole (fun v => x v ≠ y v) Finset.univ]
  simp_rw [hh, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (V → Bool))) (t := (Finset.univ : Finset V))]
  have hsum (v : V) :
      (∑ x : V → Bool, ∑ y : V → Bool,
        (μ {ω | f ω = x ∧ g ω = y}).toReal * (if x v ≠ y v then (1 : ℝ) else 0)) =
      (μ {ω | f ω v ≠ g ω v}).toReal := by
    let A : ((V → Bool) × (V → Bool)) → Set Ω := fun z =>
      if z.1 v ≠ z.2 v then {ω | f ω = z.1 ∧ g ω = z.2} else ∅
    have hm (z : (V → Bool) × (V → Bool)) : MeasurableSet (A z) := by
      dsimp [A]
      split
      · exact (measurableSet_eq.preimage hf).inter (measurableSet_eq.preimage hg)
      · exact MeasurableSet.empty
    have hd : Pairwise (Disjoint on A) := by
      intro a b hab
      apply Set.disjoint_left.mpr
      intro ω ha hb
      by_cases h1 : a.1 v ≠ a.2 v <;> by_cases h2 : b.1 v ≠ b.2 v
      · have ha' : f ω = a.1 ∧ g ω = a.2 := by simpa [A,h1] using ha
        have hb' : f ω = b.1 ∧ g ω = b.2 := by simpa [A,h2] using hb
        apply hab
        exact Prod.ext (ha'.1.symm.trans hb'.1) (ha'.2.symm.trans hb'.2)
      · simp [A,h2] at hb
      · simp [A,h1] at ha
      · simp [A,h1] at ha
    have hu : (⋃ z, A z) = {ω | f ω v ≠ g ω v} := by
      ext ω
      simp only [mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨⟨x,y⟩,hz⟩
        by_cases hxy : x v ≠ y v
        · have hz' : f ω = x ∧ g ω = y := by simpa [A,hxy] using hz
          simpa [hz'.1,hz'.2] using hxy
        · simp [A,hxy] at hz
      · intro hω
        refine ⟨(f ω,g ω), ?_⟩
        simp [A,hω]
    have hm' := measureReal_iUnion_fintype (μ := μ) hd hm
    rw [hu,Fintype.sum_prod_type] at hm'
    calc
      _ = ∑ x : V → Bool, ∑ y : V → Bool, μ.real (A (x,y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : x v ≠ y v
        · simp [A,hxy,Measure.real]
        · have hxy' : x v = y v := not_ne_iff.mp hxy
          simp [A,hxy,hxy',Measure.real]
      _ = μ.real {ω | f ω v ≠ g ω v} := hm'.symm
      _ = _ := rfl
  exact Finset.sum_le_sum (fun v _ => le_of_eq (hsum v))
