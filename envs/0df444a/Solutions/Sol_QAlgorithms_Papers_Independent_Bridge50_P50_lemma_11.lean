-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:28:37.073158+00:00
-- url     : https://prove2.me/submissions/213cbc18-34f2-4e69-8807-79a2d35bf33d

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace


end QAlgorithms.Papers.Independent.Bridge50.P50

open QAlgorithms.Papers.Independent.Bridge50.P50

theorem s110_aadc_cara {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (s : Set E) (p : E) (hp : p ∈ s) (x : E) (hx : x ∈ convexHull ℝ s) :
    ∃ q : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E),
      (∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i = 1 ∧ (∀ i, q.2 i ∈ s) ∧ ∑ i, q.1 i • q.2 i = x := by
  obtain ⟨ι, _, z, w, hz, hai, hw, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  let f : ι → Fin (Module.finrank ℝ E + 1) :=
    fun i => Fin.castLE hcard (Fintype.equivFin ι i)
  have hf : Function.Injective f := by
    intro a b hab
    simpa [f] using hab
  refine ⟨(Function.extend f w 0, Function.extend f z (fun _ => p)), ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := h
      simp only [hf.extend_apply]; exact (hw a).le
    · simp only [Function.extend_apply' _ _ _ h]; simp
  · rw [← hw1]
    symm
    apply Fintype.sum_of_injective f hf
    · intro i hi
      exact Function.extend_apply' _ _ _ (by simpa using hi)
    · intro a; simp [hf.extend_apply]
  · intro i
    by_cases h : ∃ a, f a = i
    · obtain ⟨a, rfl⟩ := h
      simp only [hf.extend_apply]; exact hz ⟨a, rfl⟩
    · simp only [Function.extend_apply' _ _ _ h]; exact hp
  · rw [← hwx]
    symm
    apply Fintype.sum_of_injective f hf
    · intro i hi
      have h : ¬∃ a, f a = i := by simpa using hi
      simp [Function.extend_apply' _ _ _ h]
    · intro a; simp [hf.extend_apply]

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    (Theta : ℕ → Set E) (hc : ∀ n, IsCompact (Theta n)) (hn : Antitone Theta)
    (hi : (⋂ n, Theta n).Nonempty) :
    (⋂ n, convexHull ℝ (Theta n)) = convexHull ℝ (⋂ n, Theta n) := by
  apply le_antisymm
  · intro x hx
    rw [Set.mem_iInter] at hx
    obtain ⟨p, hp⟩ := hi
    rw [Set.mem_iInter] at hp
    set N := Module.finrank ℝ E + 1
    let S : ℕ → Set ((Fin N → ℝ) × (Fin N → E)) := fun n =>
      {q | (∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i = 1 ∧ (∀ i, q.2 i ∈ Theta n) ∧
        ∑ i, q.1 i • q.2 i = x}
    have hS_anti : Antitone S := by
      intro a b hab q hq
      exact ⟨hq.1, hq.2.1, fun i => hn hab (hq.2.2.1 i), hq.2.2.2⟩
    have hS_closed : ∀ n, IsClosed (S n) := by
      intro n
      have h1 : IsClosed {q : (Fin N → ℝ) × (Fin N → E) | ∀ i, 0 ≤ q.1 i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
      have h2 : IsClosed {q : (Fin N → ℝ) × (Fin N → E) | ∑ i, q.1 i = 1} :=
        isClosed_eq (by fun_prop) continuous_const
      have h3 : IsClosed {q : (Fin N → ℝ) × (Fin N → E) | ∀ i, q.2 i ∈ Theta n} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => (hc n).isClosed.preimage (by fun_prop)
      have h4 : IsClosed {q : (Fin N → ℝ) × (Fin N → E) | ∑ i, q.1 i • q.2 i = x} :=
        isClosed_eq (by fun_prop) continuous_const
      exact h1.inter (h2.inter (h3.inter h4))
    have hS0 : IsCompact (S 0) := by
      have hK : IsCompact (stdSimplex ℝ (Fin N) ×ˢ Set.pi Set.univ (fun _ : Fin N => Theta 0)) :=
        (isCompact_stdSimplex ℝ (Fin N)).prod (isCompact_univ_pi fun _ => hc 0)
      apply hK.of_isClosed_subset (hS_closed 0)
      intro q hq
      exact ⟨⟨hq.1, hq.2.1⟩, fun i _ => hq.2.2.1 i⟩
    have hne : (⋂ n, S n).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · exact hS_anti.directed_ge
      · intro n
        exact s110_aadc_cara (Theta n) p (hp n) x (hx n)
      · intro n
        exact hS0.of_isClosed_subset (hS_closed n) (hS_anti (Nat.zero_le n))
      · exact hS_closed
    obtain ⟨q, hq⟩ := hne
    rw [Set.mem_iInter] at hq
    obtain ⟨hq0, hq1, -, hqx⟩ := hq 0
    rw [← hqx]
    apply (convex_convexHull ℝ _).sum_mem (fun i _ => hq0 i) hq1
    intro i _
    apply subset_convexHull
    rw [Set.mem_iInter]
    intro n
    exact (hq n).2.2.1 i
  · exact Set.subset_iInter fun n => convexHull_mono (Set.iInter_subset _ n)

end
