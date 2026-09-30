-- Prove2me | solution 1 for UnderstandingML.realizable_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T18:49:04.684986+00:00
-- url     : https://prove2.me/submissions/3f320210-4014-4c99-92d5-52d2a0f966d6

import Theorems.Thm_UnderstandingML_eps_net_theorem

open MeasureTheory

namespace UnderstandingML

/-- Shattering is invariant under XOR with a fixed labeling function. -/
lemma shatters_xor_iff_aux {X : Type*} (H : Set (X → Bool)) (f : X → Bool) (C : Finset X) :
    Shatters {g | ∃ h ∈ H, g = fun x ↦ xor (h x) (f x)} C ↔ Shatters H C := by
  constructor
  · intro hS g
    obtain ⟨g', ⟨h, hH, rfl⟩, hg'⟩ := hS (fun c ↦ xor (g c) (f c))
    refine ⟨h, hH, fun c ↦ ?_⟩
    have := hg' c
    simp only at this
    cases h1 : h c <;> cases h2 : f c <;> cases h3 : g c <;> simp_all
  · intro hS g
    obtain ⟨h, hH, hg⟩ := hS (fun c ↦ xor (g c) (f c))
    refine ⟨_, ⟨h, hH, rfl⟩, fun c ↦ ?_⟩
    have := hg c
    cases h1 : h c <;> cases h2 : f c <;> cases h3 : g c <;> simp_all

end UnderstandingML

open UnderstandingML

theorem solution {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (A : Learner (X × Bool) (X → Bool)) (hA : IsERMLearner loss01 H A) (D : Measure X)
    [IsProbabilityMeasure D] (f : X → Bool) (hf : Measurable f) (hreal : Realizable H D f)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 4) (m : ℕ)
    (hm : 8 / ε * (2 * d * Real.log (16 * Real.exp 1 / ε) + Real.log (2 / δ)) ≤ m) :
    iidLaw (labeledLaw D f) m {S | ε < trueError D f (A m S)} ≤ ENNReal.ofReal δ := by
  classical
  -- the class of error sets
  set H' : Set (X → Bool) := {g | ∃ h ∈ H, g = fun x ↦ xor (h x) (f x)} with hH'def
  have hmeasBool : ∀ g : X → Bool, Measurable g → Measurable (fun x ↦ xor (g x) (f x)) := by
    intro g hg
    have : Measurable (fun p : Bool × Bool ↦ xor p.1 p.2) := measurable_of_countable _
    exact this.comp (hg.prodMk hf)
  have hH' : ∀ g ∈ H', Measurable g := by
    rintro g ⟨h, hh, rfl⟩
    exact hmeasBool h (hH h hh)
  have hsep' : PointwiseSeparable H' := by
    obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
    refine ⟨(fun h : X → Bool ↦ fun x ↦ xor (h x) (f x)) '' H₀, ?_, hH₀c.image _, ?_⟩
    · rintro g ⟨h, hh, rfl⟩
      exact ⟨h, hH₀H hh, rfl⟩
    · rintro g ⟨h, hh, rfl⟩
      obtain ⟨u, hu, hconv⟩ := happrox h hh
      refine ⟨fun n x ↦ xor (u n x) (f x), fun n ↦ ⟨u n, hu n, rfl⟩, fun x ↦ ?_⟩
      obtain ⟨N, hN⟩ := hconv x
      exact ⟨N, fun n hn ↦ by simp [hN n hn]⟩
  have hd' : vcDim H' = d := by
    rw [← hd]
    unfold vcDim
    simp_rw [hH'def, shatters_xor_iff_aux]
  have hnet := eps_net_theorem H' hH' hsep' d hd' D ε δ hε hε1 hδ hδ1 m hm
  -- the embedding of unlabeled samples into labeled samples
  set g : (Fin m → X) → (Fin m → X × Bool) := fun S i ↦ (S i, f (S i)) with hgdef
  have hgmeas : Measurable g := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).prodMk (hf.comp (measurable_pi_apply i))
  have hgemb : MeasurableEmbedding g := by
    refine MeasurableEmbedding.of_measurable_inverse hgmeas ?_
      (g := fun S' i ↦ (S' i).1) ?_ ?_
    · have : Set.range g = ⋂ i, {S' : Fin m → X × Bool | (S' i).2 = f (S' i).1} := by
        ext S'
        simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · rintro ⟨S, rfl⟩ i
          rfl
        · intro h
          refine ⟨fun i ↦ (S' i).1, ?_⟩
          funext i
          exact Prod.ext rfl (h i).symm
      rw [this]
      refine MeasurableSet.iInter fun i ↦ ?_
      exact measurableSet_eq_fun ((measurable_pi_apply i).snd)
        (hf.comp (measurable_pi_apply i).fst)
    · rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply i).fst
    · intro S
      rfl
  have hlaw : iidLaw (labeledLaw D f) m = (iidLaw D m).map g := by
    unfold iidLaw labeledLaw
    rw [Measure.pi_map_pi (f := fun _ x ↦ (x, f x))]
    intro i
    exact (measurable_id.prodMk hf).aemeasurable
  rw [hlaw, hgemb.map_apply]
  -- the null set where some sample point is misclassified by the target hypothesis
  obtain ⟨hstar, hstarH, hstar0⟩ := hreal
  set Z : Set X := {x | hstar x ≠ f x} with hZ
  have hZ0 : D Z = 0 := by
    unfold trueError at hstar0
    rcases (ENNReal.toReal_eq_zero_iff _).1 hstar0 with h | h
    · exact h
    · exact absurd h (measure_ne_top D _)
  have hnull : iidLaw D m {S | ∃ i, S i ∈ Z} = 0 := by
    have : {S : Fin m → X | ∃ i, S i ∈ Z} = ⋃ i, Function.eval i ⁻¹' Z := by
      ext S; simp
    rw [this]
    refine measure_iUnion_null fun i ↦ ?_
    exact Measure.pi_eval_preimage_null _ hZ0
  have hsub : g ⁻¹' {S | ε < trueError D f (A m S)} ⊆
      {S | ¬ IsEpsNet H' D ε S} ∪ {S | ∃ i, S i ∈ Z} := by
    intro S hS
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hS
    by_cases hZS : ∃ i, S i ∈ Z
    · exact Or.inr hZS
    left
    push Not at hZS
    have hERM := hA m (g S)
    -- the target hypothesis has zero empirical risk
    have hstar_emp : empRisk loss01 (g S) hstar = 0 := by
      unfold empRisk
      have : ∀ i, loss01 hstar (g S i) = 0 := by
        intro i
        have := hZS i
        simp only [hZ, Set.mem_setOf_eq, ne_eq, not_not] at this
        simp [loss01, hgdef, this]
      simp [this]
    have hA_emp : empRisk loss01 (g S) (A m (g S)) ≤ 0 := by
      have := hERM.2 hstar hstarH
      rw [hstar_emp] at this
      exact this
    -- hence the ERM output is correct on every sample point
    have hcorrect : ∀ i, A m (g S) (S i) = f (S i) := by
      intro i
      by_contra hne
      have hpos : ∀ j, 0 ≤ loss01 (A m (g S)) (g S j) := by
        intro j; unfold loss01; split_ifs <;> norm_num
      have hone : loss01 (A m (g S)) (g S i) = 1 := by
        show loss01 _ (S i, f (S i)) = 1
        simp [loss01, hne]
      have hmpos : (0 : ℝ) < m := by
        have : 0 < m := Fin.pos i
        exact_mod_cast this
      have : (0 : ℝ) < empRisk loss01 (g S) (A m (g S)) := by
        unfold empRisk
        apply div_pos _ hmpos
        calc (0 : ℝ) < loss01 (A m (g S)) (g S i) := by rw [hone]; norm_num
          _ ≤ ∑ j, loss01 (A m (g S)) (g S j) :=
            Finset.single_le_sum (fun j _ ↦ hpos j) (Finset.mem_univ i)
      linarith
    intro hnet'
    have hmem : (fun x ↦ xor (A m (g S) x) (f x)) ∈ H' := ⟨A m (g S), hERM.1, rfl⟩
    have hbig : ENNReal.ofReal ε ≤ D {x | xor (A m (g S) x) (f x) = true} := by
      have hset : {x | xor (A m (g S) x) (f x) = true} = {x | A m (g S) x ≠ f x} := by
        ext x; simp
      rw [hset]
      unfold trueError at hS
      have := ENNReal.ofReal_le_ofReal hS.le
      rw [ENNReal.ofReal_toReal (measure_ne_top D _)] at this
      exact this
    obtain ⟨i, hi⟩ := hnet' _ hmem hbig
    rw [hcorrect i] at hi
    simp at hi
  calc iidLaw D m (g ⁻¹' {S | ε < trueError D f (A m S)})
      ≤ iidLaw D m ({S | ¬ IsEpsNet H' D ε S} ∪ {S | ∃ i, S i ∈ Z}) := measure_mono hsub
    _ ≤ iidLaw D m {S | ¬ IsEpsNet H' D ε S} + iidLaw D m {S | ∃ i, S i ∈ Z} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal δ := by rw [hnull, add_zero]; exact hnet
