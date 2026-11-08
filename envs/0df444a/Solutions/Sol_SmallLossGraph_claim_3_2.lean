-- Prove2me | solution 1 for SmallLossGraph.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:31:04.243369+00:00
-- url     : https://prove2.me/submissions/b9b19202-9e27-49f4-a876-b66c4a4a0327

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

open SmallLossGraph in
theorem solution {d : ℕ} (G : SimpleGraph (Fin d)) (α : ℕ) (hα : SmallLossGraph.IndepBound G α)
    (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (γ : ℝ) (hγ : 0 < γ) :
    ∑ i ∈ SmallLossGraph.frozen0 G p γ, p i ≤ (α : ℝ) * γ := by
  classical
  have aux : ∀ I : Finset (Fin d), ∑ x ∈ I.biUnion (SmallLossGraph.closedNbhd G), p x ≤
      ∑ v ∈ I, ∑ x ∈ SmallLossGraph.closedNbhd G v, p x := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := Finset.sum_union_inter (s₁ := SmallLossGraph.closedNbhd G a)
        (s₂ := s.biUnion (SmallLossGraph.closedNbhd G)) (f := p)
      have h0 : 0 ≤ ∑ x ∈ SmallLossGraph.closedNbhd G a ∩ s.biUnion (SmallLossGraph.closedNbhd G), p x :=
        Finset.sum_nonneg (fun i _ => hp i)
      linarith
  have memF : ∀ v, v ∈ SmallLossGraph.frozen0 G p γ ↔
      ∑ j ∈ SmallLossGraph.closedNbhd G v, p j < γ := by
    intro v
    unfold SmallLossGraph.frozen0
    simp
  let C := (SmallLossGraph.frozen0 G p γ).powerset.filter
    (fun I : Finset (Fin d) => G.IsIndepSet (I : Set (Fin d)))
  have hCne : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨I, hIC, hImax⟩ := C.exists_max_image Finset.card hCne
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hIC
  obtain ⟨hIF, hIind⟩ := hIC
  have hdom : SmallLossGraph.frozen0 G p γ ⊆ I.biUnion (SmallLossGraph.closedNbhd G) := by
    intro i hi
    rw [Finset.mem_biUnion]
    by_contra hno
    push_neg at hno
    have hnb : ∀ v ∈ I, ¬ (i = v ∨ G.Adj v i) := by
      intro v hv h
      apply hno v hv
      unfold SmallLossGraph.closedNbhd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    have hiI : i ∉ I := fun h => hnb i h (Or.inl rfl)
    have hind' : G.IsIndepSet ((insert i I : Finset (Fin d)) : Set (Fin d)) := by
      rw [Finset.coe_insert]
      show (insert i (I : Set (Fin d))).Pairwise (fun v w => ¬ G.Adj v w)
      rw [Set.pairwise_insert]
      refine ⟨hIind, fun b hb _ => ⟨fun h => hnb b hb (Or.inr h.symm), fun h => hnb b hb (Or.inr h)⟩⟩
    have hmem : insert i I ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hi hIF, hind'⟩
    have := hImax _ hmem
    rw [Finset.card_insert_of_notMem hiI] at this
    omega
  have hcard : (I.card : ℝ) ≤ α := by exact_mod_cast hα I hIind
  calc ∑ i ∈ SmallLossGraph.frozen0 G p γ, p i
      ≤ ∑ x ∈ I.biUnion (SmallLossGraph.closedNbhd G), p x :=
        Finset.sum_le_sum_of_subset_of_nonneg hdom (fun i _ _ => hp i)
    _ ≤ ∑ v ∈ I, ∑ x ∈ SmallLossGraph.closedNbhd G v, p x := aux I
    _ ≤ ∑ v ∈ I, γ := Finset.sum_le_sum (fun v hv => ((memF v).1 (hIF hv)).le)
    _ = (I.card : ℝ) * γ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (α : ℝ) * γ := mul_le_mul_of_nonneg_right hcard hγ.le
