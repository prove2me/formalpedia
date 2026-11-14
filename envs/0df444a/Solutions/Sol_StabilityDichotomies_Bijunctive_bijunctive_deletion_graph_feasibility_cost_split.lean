-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_deletion_graph_feasibility_cost_split
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:50:06.04081+00:00
-- url     : https://prove2.me/submissions/a8de7a8c-8432-4711-8e28-84b9f78a6aa6

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_exact_law_deletion_shared_seed_coupling
import Theorems.Thm_StabilityDichotomies_Solvability_delete_thinned_mask_alignment
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (j : Fin I.constraints.card) (ε : ℝ) (hε : 0 < ε)
    (A : Solver Γ) (hLaw : BijunctiveOutputLaw Γ rep ε A)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete (occurrenceAt I j)).constraints.card))
    (hej : e j = none)
    (he : ∀ k, (e k).elim (occurrenceAt I j) (occurrenceAt (I.delete (occurrenceAt I j))) = occurrenceAt I k) :
    let μ := bijunctiveSeedMeasure rep I ε
    let G := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
    let F := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
    let Fminus := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
    let mid := fun z v => decide (literalScore rep (G z) (F z) z.2.2 (v,false) < literalScore rep (G z) (F z) z.2.2 (v,true))
    let last := fun z v => decide (literalScore rep (G z) (Fminus z) z.2.2 (v,false) < literalScore rep (G z) (Fminus z) z.2.2 (v,true))
    wasserstein (A V I) (A V (I.delete (occurrenceAt I j))) ≤
      (∑ v : V, (μ {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid z v}).toReal) +
      (∑ v : V, (μ {z | mid z v ≠ last z v}).toReal) := by
  classical
  let c := occurrenceAt I j
  let Ω := (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let μ : Measure Ω := bijunctiveSeedMeasure rep I ε
  let G := fun z : Ω => thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
  let F := fun z : Ω => thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
  let Fminus := fun z : Ω => thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
  let mid := fun z v => decide (literalScore rep (G z) (F z) z.2.2 (v,false) < literalScore rep (G z) (F z) z.2.2 (v,true))
  let last := fun z v => decide (literalScore rep (G z) (Fminus z) z.2.2 (v,false) < literalScore rep (G z) (Fminus z) z.2.2 (v,true))
  haveI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  have hc : c ∈ I.constraints := by
    unfold c occurrenceAt
    exact Multiset.mem_toList.mp (List.get_mem _ _)
  have hej' : e.symm none = j := by
    apply e.injective
    simpa using hej.symm
  have halign (mask : Fin I.constraints.card → Bool) :
      thinnedInstance I (fun i => mask i && decide (i ≠ j)) =
      thinnedInstance (I.delete c) (fun k => mask (e.symm (some k))) := by
    have hm : (fun i => mask i && decide (i ≠ j)) = Function.update mask (e.symm none) false := by
      rw [hej']
      funext i
      by_cases hij : i = j
      · subst i; simp
      · simp [Function.update_of_ne hij,hij]
    rw [hm]
    exact delete_thinned_mask_alignment I c hc e he mask
  have hlast (z : Ω) (v : V) :
      bijunctiveOutput rep (I.delete c) ε (fun i => z.1 (e.symm (some i))) z.2.1 z.2.2 v = last z v := by
    unfold bijunctiveOutput last G Fminus
    rw [← halign (fun i => decide (z.1 i ≤ 1 - ε / 2)), ← halign (fun i => decide (z.1 i ≤ z.2.1))]
  have hcoup := bijunctive_exact_law_deletion_shared_seed_coupling rep I c hc hI ε hε A hLaw e
  change wasserstein (A V I) (A V (I.delete c)) ≤ _
  refine hcoup.trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  let E : Set Ω := {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠
    bijunctiveOutput rep (I.delete c) ε (fun i => z.1 (e.symm (some i))) z.2.1 z.2.2 v}
  let B : Set Ω := {z | bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v ≠ mid z v}
  let C : Set Ω := {z | mid z v ≠ last z v}
  have hsub : E ⊆ B ∪ C := by
    intro z hz
    by_contra hnot
    have h1 : bijunctiveOutput rep I ε z.1 z.2.1 z.2.2 v = mid z v := by
      by_contra hn; exact hnot (Or.inl hn)
    have h2 : mid z v = last z v := by
      by_contra hn; exact hnot (Or.inr hn)
    apply hz
    rw [hlast z v]
    exact h1.trans h2
  exact (measureReal_mono hsub).trans (measureReal_union_le B C)
