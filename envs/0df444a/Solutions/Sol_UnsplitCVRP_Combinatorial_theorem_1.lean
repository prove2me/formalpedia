-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:54:06.554191+00:00
-- url     : https://prove2.me/submissions/6e33393c-45ff-4d08-90d4-653be3409365

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_6
import Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_10
import Theorems.Thm_UnsplitCVRP_Combinatorial_lemma_11
import Theorems.Thm_UnsplitCVRP_Combinatorial_eq_4
import Theorems.Thm_UnsplitCVRP_Combinatorial_eq_5

namespace CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial

theorem finite_lists {α : Type} [Finite α] (m : ℕ) :
    {R : List (List α) | R.length ≤ m ∧ ∀ L ∈ R, L.length ≤ m}.Finite := by
  have hS' := List.finite_length_le α m
  have : Finite ↥{l : List α | l.length ≤ m} := hS'.to_subtype
  have hF := (List.finite_length_le (↥{l : List α | l.length ≤ m}) m).image
    (fun l => l.map Subtype.val)
  refine hF.subset ?_
  rintro R ⟨hRl, hR⟩
  lift R to List ↥{l : List α | l.length ≤ m} using hR
  exact ⟨R, by simpa using hRl, rfl⟩

theorem finite_sols {n : ℕ} :
    {R : List (List (Fin (n + 1))) | (∀ L ∈ R, L ≠ []) ∧ R.flatten.Nodup}.Finite := by
  refine (finite_lists (α := Fin (n + 1)) (n + 1)).subset ?_
  rintro R ⟨hne, hnd⟩
  have hlen : R.flatten.length ≤ n + 1 := by
    simpa using hnd.length_le_card
  refine ⟨?_, ?_⟩
  · have : R.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      calc R.length = (R.map (fun _ => 1)).sum := by simp
        _ ≤ (R.map List.length).sum := by
          apply List.sum_le_sum
          intro L hL
          exact List.length_pos_iff.mpr (hne L hL)
    omega
  · intro L hL
    have : L.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      exact List.le_sum_of_mem (List.mem_map_of_mem hL)
    omega

theorem sInf_attained {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (hne : ∃ x, P x) :
    ∃ x, P x ∧ f x = sInf {t | ∃ x, P x ∧ t = f x} := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  obtain ⟨x0, hx0⟩ := hne
  have hmem := Set.Nonempty.csInf_mem (s := f '' {x | P x}) ⟨f x0, x0, hx0, rfl⟩
    (hfin.image f)
  rw [hT]
  obtain ⟨x, hx, hfx⟩ := hmem
  exact ⟨x, hx, hfx⟩

theorem sInf_le_of {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (x : β) (hx : P x) :
    sInf {t | ∃ x, P x ∧ t = f x} ≤ f x := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [hT]
  exact csInf_le (hfin.image f).bddBelow ⟨x, hx, rfl⟩

end CVRPAux

namespace CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial

theorem bestSplit_attained {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (A : List (Fin (n + 1))) (hAn : A.Nodup)
    (hA1 : ∀ a ∈ A, d a ≤ 1) :
    ∃ R, IsConsecutiveSplit d A R ∧ solutionCost c R = bestSplit c d A := by
  unfold bestSplit
  apply sInf_attained
  · refine finite_sols.subset ?_
    rintro R ⟨hfl, hR⟩
    exact ⟨fun L hL => (hR L hL).1, hfl ▸ hAn⟩
  · refine ⟨A.map (fun a => [a]), ?_, ?_⟩
    · clear hAn hA1
      induction A with
      | nil => rfl
      | cons a t ih => simp [ih]
    · intro L hL
      simp only [List.mem_map] at hL
      obtain ⟨a, ha, rfl⟩ := hL
      exact ⟨by simp, by simpa [load] using hA1 a ha⟩

theorem matchCost_attained {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (B : Finset (Fin (n + 1))) (hB0 : (0 : Fin (n + 1)) ∉ B)
    (hB1 : ∀ a ∈ B, d a ≤ 1) :
    ∃ R, (IsSolutionOn d B R ∧ (∀ L ∈ R, L.length ≤ 2)) ∧
      solutionCost c R = matchCost c d B := by
  unfold matchCost
  have := sInf_attained (fun R => IsSolutionOn d B R ∧ (∀ L ∈ R, L.length ≤ 2))
    (solutionCost c) ?_ ?_
  · obtain ⟨R, hR, h⟩ := this
    refine ⟨R, hR, ?_⟩
    rw [h]; congr 1; ext t; simp [and_assoc]
  · refine finite_sols.subset ?_
    rintro R ⟨⟨hR, hnd, _⟩, _⟩
    exact ⟨fun L hL => (hR L hL).1, hnd⟩
  · refine ⟨B.toList.map (fun a => [a]), ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · intro L hL
      simp only [List.mem_map] at hL
      obtain ⟨a, ha, rfl⟩ := hL
      have ha' : a ∈ B := Finset.mem_toList.mp ha
      refine ⟨by simp, ?_, by simpa [load] using hB1 a ha'⟩
      simp only [List.mem_singleton]
      rintro rfl; exact hB0 ha'
    · have : (B.toList.map (fun a => [a])).flatten = B.toList := by
        generalize B.toList = A
        induction A with
        | nil => rfl
        | cons a t ih => simp [ih]
      rw [this]; exact B.nodup_toList
    · intro v
      have : (B.toList.map (fun a => [a])).flatten = B.toList := by
        generalize B.toList = A
        induction A with
        | nil => rfl
        | cons a t ih => simp [ih]
      rw [this]; simp
    · intro L hL
      simp only [List.mem_map] at hL
      obtain ⟨a, ha, rfl⟩ := hL
      simp

theorem radial_split {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (δ : ℝ) (S : Finset (Fin (n + 1))) :
    radial c d S = radial c d (smallIn d δ S) + radial c d (bigIn d δ S) := by
  unfold radial smallIn bigIn
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => d v ≤ δ)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext v; simp [not_le]

end CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial CVRPAux in
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (α : ℝ) (hα : 1 ≤ α)
    (As Aa : List (Fin (n + 1)))
    (hAs : IsTourOn (smallIn d (1 / 3 : ℝ) (clients n)) As)
    (hAa : IsTourOn (clients n) Aa)
    (hcAs : SupplyChainTheory.routeCost c As ≤
      α * tspOn c (smallIn d (1 / 3 : ℝ) (clients n)))
    (hcAa : SupplyChainTheory.routeCost c Aa ≤ α * tspOn c (clients n)) :
    (∃ R, IsSolution d R ∧
      SupplyChainTheory.solutionCost c R = alg1Cost c d As Aa) ∧
    ∀ R, IsSolution d R →
      alg1Cost c d As Aa ≤ (α + 7 / 4) * SupplyChainTheory.solutionCost c R := by
  have hcl : ∀ v, v ∈ clients n ↔ v ≠ 0 := by intro v; simp [clients]
  refine ⟨?_, ?_⟩
  · -- the two candidate solutions are feasible and attain their costs
    obtain ⟨RS, hRS, hRSc⟩ := bestSplit_attained c d As hAs.1 (by
      intro a ha
      have := (hAs.2 a).1 ha
      simp only [smallIn, Finset.mem_filter] at this
      exact (hd a ((hcl a).1 this.1)).2)
    obtain ⟨RA, hRA, hRAc⟩ := bestSplit_attained c d Aa hAa.1 (by
      intro a ha
      exact (hd a ((hcl a).1 ((hAa.2 a).1 ha))).2)
    obtain ⟨RM, ⟨hRM, _⟩, hRMc⟩ := matchCost_attained c d
      (bigIn d (1 / 3 : ℝ) (clients n)) (by simp [bigIn, clients]) (by
        intro a ha
        simp only [bigIn, Finset.mem_filter] at ha
        exact (hd a ((hcl a).1 ha.1)).2)
    unfold alg1Cost
    rcases min_choice (matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) + bestSplit c d As)
      (bestSplit c d Aa) with h | h <;> rw [h]
    · refine ⟨RM ++ RS, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro L hL
        rcases List.mem_append.mp hL with hL | hL
        · exact hRM.1 L hL
        · obtain ⟨hne, hload⟩ := hRS.2 L hL
          refine ⟨hne, ?_, hload⟩
          intro h0
          have : (0 : Fin (n + 1)) ∈ As := by
            rw [← hRS.1]; exact List.mem_flatten.mpr ⟨L, hL, h0⟩
          have := (hAs.2 0).1 this
          simp [smallIn, clients] at this
      · rw [List.flatten_append, List.nodup_append]
        refine ⟨hRM.2.1, hRS.1 ▸ hAs.1, ?_⟩
        intro a ha b hb hab
        subst hab
        have h1 := (hRM.2.2 a).1 ha
        rw [hRS.1] at hb
        have h2 := (hAs.2 a).1 hb
        simp only [bigIn, smallIn, Finset.mem_filter] at h1 h2
        linarith [h1.2, h2.2]
      · intro v
        rw [List.flatten_append, List.mem_append, hRS.1, hRM.2.2 v, hAs.2 v]
        simp only [bigIn, smallIn, Finset.mem_filter]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro h
          by_cases hv : d v ≤ 1 / 3
          · exact Or.inr ⟨h, hv⟩
          · exact Or.inl ⟨h, lt_of_not_ge hv⟩
      · simp [solutionCost, List.map_append, List.sum_append] at hRMc hRSc ⊢
        rw [hRMc, hRSc]
    · refine ⟨RA, ⟨?_, ?_, ?_⟩, hRAc⟩
      · intro L hL
        obtain ⟨hne, hload⟩ := hRA.2 L hL
        refine ⟨hne, ?_, hload⟩
        intro h0
        have : (0 : Fin (n + 1)) ∈ Aa := by
          rw [← hRA.1]; exact List.mem_flatten.mpr ⟨L, hL, h0⟩
        have := (hAa.2 0).1 this
        simp [clients] at this
      · rw [hRA.1]; exact hAa.1
      · intro v; rw [hRA.1]; exact hAa.2 v
  · intro R hR
    have h6 := lemma_6 c hc d hd R hR
    have h10 := lemma_10 c hc d hd R hR
    have h11 := lemma_11 c hc d hd
    have h4 := eq_4 c hc d hd α hα As hAs hcAs R hR
    have h5 := eq_5 c hc d hd α hα Aa hAa hcAa R hR
    have hsplit := radial_split c d (1 / 3 : ℝ) (clients n)
    unfold alg1Cost
    have hm1 := min_le_left (matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) +
      bestSplit c d As) (bestSplit c d Aa)
    have hm2 := min_le_right (matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) +
      bestSplit c d As) (bestSplit c d Aa)
    linarith
