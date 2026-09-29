-- Prove2me | solution 1 for Supermodularity.Cooperative.convex_game_iff_totally_large_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T13:42:53.907897+00:00
-- url     : https://prove2.me/submissions/d7644bfa-3515-4dba-ab2b-48f847883d2b

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_IsTotallyLargeCore

set_option autoImplicit false

lemma smc_tight_union {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B))
    (U : Finset (Fin n)) (y : Fin n → ℝ) (hacc : ∀ S ⊆ U, f S ≤ ∑ i ∈ S, y i)
    {A B : Finset (Fin n)} (hA : A ⊆ U) (hB : B ⊆ U)
    (tA : ∑ i ∈ A, y i = f A) (tB : ∑ i ∈ B, y i = f B) :
    ∑ i ∈ A ∪ B, y i = f (A ∪ B) := by
  have h1 : ∑ i ∈ A ∪ B, y i + ∑ i ∈ A ∩ B, y i = ∑ i ∈ A, y i + ∑ i ∈ B, y i :=
    Finset.sum_union_inter
  have h2 := hsup A B
  have h3 := hacc (A ∪ B) (Finset.union_subset hA hB)
  have h4 := hacc (A ∩ B) (Finset.inter_subset_left.trans hA)
  linarith

lemma smc_cover_tight {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B))
    (U : Finset (Fin n)) (y : Fin n → ℝ) (hacc : ∀ S ⊆ U, f S ≤ ∑ i ∈ S, y i)
    (hcov : ∀ i ∈ U, ∃ S ⊆ U, i ∈ S ∧ ∑ j ∈ S, y j = f S) :
    ∑ i ∈ U, y i = f U := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Finset (Finset (Fin n)),
      F = U.powerset.filter (fun S => ∑ j ∈ S, y j = f S) := ⟨_, rfl⟩
  have hM : F.sup id ⊆ U ∧ ∑ i ∈ F.sup id, y i = f (F.sup id) := by
    apply Finset.sup_induction (p := fun S => S ⊆ U ∧ ∑ i ∈ S, y i = f S)
    · refine ⟨Finset.empty_subset _, ?_⟩
      simp [hf0]
    · intro a₁ h₁ a₂ h₂
      exact ⟨Finset.union_subset h₁.1 h₂.1,
        smc_tight_union f hsup U y hacc h₁.1 h₂.1 h₁.2 h₂.2⟩
    · intro S hS
      rw [hF, Finset.mem_filter, Finset.mem_powerset] at hS
      exact hS
  have hUM : U ⊆ F.sup id := by
    intro i hi
    obtain ⟨S, hSU, hiS, hSt⟩ := hcov i hi
    have hSF : S ∈ F := by
      rw [hF, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hSU, hSt⟩
    exact Finset.le_sup (f := id) hSF hiS
  have hEq : F.sup id = U := Finset.Subset.antisymm hM.1 hUM
  have := hM.2
  rw [hEq] at this
  exact this

open Supermodularity.Cooperative in
lemma smc_large_aux {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B))
    (U : Finset (Fin n)) (P : Finset (Fin n)) :
    ∀ y : Fin n → ℝ, (∀ S ⊆ U, f S ≤ ∑ i ∈ S, y i) →
      (∀ i ∈ U, i ∉ P → ∃ S ⊆ U, i ∈ S ∧ ∑ j ∈ S, y j = f S) →
      ∃ y' ∈ Core U f, ∀ i ∈ U, y' i ≤ y i := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro y hacc hcov
    refine ⟨y, ?_, fun i _ => le_refl _⟩
    simp only [Core, Set.mem_setOf_eq]
    exact ⟨smc_cover_tight f hf0 hsup U y hacc
      (fun i hi => hcov i hi (Finset.notMem_empty i)), hacc⟩
  | insert a P ha ih =>
    intro y hacc hcov
    by_cases haU : a ∈ U
    · obtain ⟨S₀, hS₀F, hmin⟩ := (U.powerset.filter (fun S => a ∈ S)).exists_min_image
        (fun S => ∑ j ∈ S, y j - f S)
        ⟨U, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨subset_refl _, haU⟩⟩
      rw [Finset.mem_filter, Finset.mem_powerset] at hS₀F
      obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ∑ j ∈ S₀, y j - f S₀ := ⟨_, rfl⟩
      have hδ0 : 0 ≤ δ := by have := hacc S₀ hS₀F.1; linarith
      have hminS : ∀ S ⊆ U, a ∈ S → δ ≤ ∑ j ∈ S, y j - f S := by
        intro S hSU haS
        rw [hδ]
        exact hmin S (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hSU, haS⟩)
      obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Fin n → ℝ, y₁ = fun j => y j - if j = a then δ else 0 :=
        ⟨_, rfl⟩
      have hsum : ∀ S : Finset (Fin n),
          ∑ j ∈ S, y₁ j = ∑ j ∈ S, y j - if a ∈ S then δ else 0 := by
        intro S
        rw [hy₁, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      have hacc₁ : ∀ S ⊆ U, f S ≤ ∑ j ∈ S, y₁ j := by
        intro S hSU
        rw [hsum S]
        split_ifs with haS
        · have := hminS S hSU haS; linarith
        · have := hacc S hSU; linarith
      have hcov₁ : ∀ i ∈ U, i ∉ P → ∃ S ⊆ U, i ∈ S ∧ ∑ j ∈ S, y₁ j = f S := by
        intro i hi hiP
        by_cases hia : i = a
        · refine ⟨S₀, hS₀F.1, hia ▸ hS₀F.2, ?_⟩
          rw [hsum S₀, if_pos hS₀F.2]
          linarith
        · obtain ⟨S, hSU, hiS, hSt⟩ := hcov i hi (by
            rw [Finset.mem_insert, not_or]; exact ⟨hia, hiP⟩)
          refine ⟨S, hSU, hiS, ?_⟩
          rw [hsum S]
          split_ifs with haS
          · have := hminS S hSU haS; linarith
          · linarith
      obtain ⟨y', hy'C, hy'le⟩ := ih y₁ hacc₁ hcov₁
      refine ⟨y', hy'C, fun i hi => (hy'le i hi).trans ?_⟩
      rw [hy₁]
      dsimp only
      split_ifs <;> linarith
    · apply ih y hacc
      intro i hi hiP
      apply hcov i hi
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => haU (h ▸ hi), hiP⟩

lemma smc_big {n : ℕ} (f : Finset (Fin n) → ℝ) (A : Finset (Fin n)) (x : Fin n → ℝ)
    (hx : ∀ S ⊆ A, f S ≤ ∑ i ∈ S, x i) (S : Finset (Fin n)) :
    f S ≤ ∑ i ∈ S, (if i ∈ A then x i
      else (∑ T : Finset (Fin n), |f T|) + ∑ j ∈ A, |x j|) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∑ T : Finset (Fin n), |f T|) + ∑ j ∈ A, |x j| :=
    ⟨_, rfl⟩
  rw [← hK]
  by_cases hSA : S ⊆ A
  · rw [Finset.sum_congr rfl (fun i hi => if_pos (hSA hi))]
    exact hx S hSA
  · obtain ⟨j, hjS, hjA⟩ := Finset.not_subset.mp hSA
    rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    have hcard : (1 : ℝ) ≤ ((S.filter (fun i => i ∉ A)).card : ℝ) := by
      have hne : (S.filter (fun i => i ∉ A)).Nonempty :=
        ⟨j, by rw [Finset.mem_filter]; exact ⟨hjS, hjA⟩⟩
      exact_mod_cast hne.card_pos
    have hC : f S ≤ ∑ T : Finset (Fin n), |f T| :=
      (le_abs_self _).trans
        (Finset.single_le_sum (fun T _ => abs_nonneg (f T)) (Finset.mem_univ S))
    have h1 : |∑ i ∈ S.filter (fun i => i ∈ A), x i| ≤
        ∑ i ∈ S.filter (fun i => i ∈ A), |x i| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ i ∈ S.filter (fun i => i ∈ A), |x i| ≤ ∑ j ∈ A, |x j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => (Finset.mem_filter.mp hi).2) (fun _ _ _ => abs_nonneg _)
    have h3 := neg_abs_le (∑ i ∈ S.filter (fun i => i ∈ A), x i)
    have hA0 : 0 ≤ ∑ j ∈ A, |x j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hK0 : 0 ≤ K := by
      rw [hK]
      have : 0 ≤ ∑ T : Finset (Fin n), |f T| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    have h4 := mul_le_mul_of_nonneg_right hcard hK0
    have h5 : K = (∑ T : Finset (Fin n), |f T|) + ∑ j ∈ A, |x j| := hK
    linarith

open Supermodularity.Cooperative in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf0 : f ∅ = 0)
    (hsuper : ∀ S1 S2 : Finset (Fin n), Disjoint S1 S2 → f S1 + f S2 ≤ f (S1 ∪ S2)) :
    IsConvexGame f ↔ IsTotallyLargeCore f := by
  classical
  constructor
  · rintro ⟨-, hsm⟩ U y hacc
    unfold Supermodularity.Monotonicity.SupermodularOn at hsm
    have hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B) :=
      fun A B => hsm (Set.mem_univ A) (Set.mem_univ B)
    exact smc_large_aux f hf0 hsup U U y hacc (fun i hi hiU => absurd hi hiU)
  · intro hT
    refine ⟨hf0, fun A _ B _ => ?_⟩
    show f A + f B ≤ f (A ∪ B) + f (A ∩ B)
    have h1 := smc_big f ∅ (fun _ => (0 : ℝ)) (by
      intro S hS
      rw [Finset.subset_empty.mp hS, hf0]
      simp)
    obtain ⟨z, hz, -⟩ := hT (A ∩ B) _ (fun S _ => h1 S)
    simp only [Core, Set.mem_setOf_eq] at hz
    have h2 := smc_big f (A ∩ B) z (fun S hS => hz.2 S hS)
    obtain ⟨w, hw, hwle⟩ := hT (A ∪ B) _ (fun S _ => h2 S)
    simp only [Core, Set.mem_setOf_eq] at hw
    have hle : ∑ i ∈ A ∩ B, w i ≤ ∑ i ∈ A ∩ B, z i := by
      apply Finset.sum_le_sum
      intro i hi
      have := hwle i (Finset.mem_union_left _ (Finset.mem_inter.mp hi).1)
      rw [if_pos hi] at this
      exact this
    have e : ∑ i ∈ A ∪ B, w i + ∑ i ∈ A ∩ B, w i = ∑ i ∈ A, w i + ∑ i ∈ B, w i :=
      Finset.sum_union_inter
    have hA := hw.2 A Finset.subset_union_left
    have hB := hw.2 B Finset.subset_union_right
    have hU := hw.1
    have hzc := hz.1
    linarith
