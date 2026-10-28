-- Prove2me | solution 2 for UnrelatedSched.TwoApprox.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:22.720074+00:00
-- url     : https://prove2.me/submissions/1663a075-fb6a-4948-b740-04f79e807e15

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm
import Theorems.Thm_UnrelatedSched_TwoApprox_theorem_1

-- carved verbatim out of submission fc87e75b-9b6a-4599-8a7c-b8d040233d56, lines 591-598

section
open MatousekLP.Scheduling
open UnrelatedSched
open UnrelatedSched.TwoApprox

lemma e57_load_le_makespan {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) (i : Fin m) :
    load (realTimes P) σ i ≤ makespan (realTimes P) σ :=
  le_ciSup (f := fun i => load (realTimes P) σ i) (Set.finite_range _).bddAbove i

theorem yes_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (d : ℝ)
    (σ : Fin n → Fin m) (hσ : makespan (realTimes P) σ ≤ d) :
    assignmentMatrix σ ∈ LPPolytope P (fun _ => d) d := by
  classical
  have hload : ∀ i, ∑ j, (P i j : ℝ) * assignmentMatrix σ i j = load (realTimes P) σ i := by
    intro i
    unfold load assignmentMatrix realTimes
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : σ j = i <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases h : σ j = i
    · exfalso
      have h1 : (P i j : ℝ) ≤ load (realTimes P) σ i := by
        unfold load realTimes
        apply Finset.single_le_sum (f := fun j => (P i j : ℝ)) (fun _ _ => by positivity)
        simp [h]
      have := e57_load_le_makespan P σ i
      linarith
    · simp [assignmentMatrix, h]
  · intro j
    simp [assignmentMatrix]
  · intro i
    rw [hload]
    exact (e57_load_le_makespan P σ i).trans hσ
  · intro i j
    unfold assignmentMatrix
    split_ifs <;> norm_num

lemma e57_makespan_eq {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) :
    makespan (realTimes P) σ = ((natMakespan P σ : ℕ) : ℝ) := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · simp [makespan, natMakespan]
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
      Finset.univ_nonempty (fun i => natLoad P σ i)
    have hload : ∀ i, load (realTimes P) σ i = ((natLoad P σ i : ℕ) : ℝ) := by
      intro i
      simp [load, natLoad, realTimes]
    have hN : natMakespan P σ = natLoad P σ i0 := hi0
    apply le_antisymm
    · apply Real.iSup_le _ (by positivity)
      intro i
      rw [hload]
      have : natLoad P σ i ≤ natMakespan P σ :=
        Finset.le_sup (f := fun i => natLoad P σ i) (Finset.mem_univ i)
      exact_mod_cast this
    · rw [hN, ← hload]
      exact e57_load_le_makespan P σ i0

lemma e57_loop {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (D : DecisionProcedure m n) (M : ℕ)
    (hsome : ∀ d σ, D d = some σ → (natMakespan P σ : ℝ) ≤ ρ * (d : ℝ))
    (hnone : ∀ d, D d = none → d < M) :
    ∀ (k l u : ℕ) (best : Fin n → Fin m), u - l ≤ k → l ≤ M →
      (natMakespan P best : ℝ) ≤ ρ * (u : ℝ) →
      (natMakespan P (searchLoop P D l u best) : ℝ) ≤ ρ * (M : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro l u best hk hl hb
    have hnl : ¬ l < u := by omega
    rw [searchLoop, dif_neg hnl]
    refine hb.trans ?_
    have : (u : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : u ≤ M)
    nlinarith
  | succ k ih =>
    intro l u best hk hl hb
    by_cases hlu : l < u
    · rw [searchLoop, dif_pos hlu]
      rcases hDd : D ((u + l) / 2) with _ | σ
      · simp only [hDd]
        have := hnone _ hDd
        exact ih _ _ _ (by omega) (by omega) hb
      · simp only [hDd]
        apply ih _ _ _ (by omega) hl
        have h1 := hsome _ σ hDd
        split_ifs with hc
        · exact h1
        · push_neg at hc
          have : (natMakespan P best : ℝ) ≤ natMakespan P σ := by exact_mod_cast hc
          linarith
    · rw [searchLoop, dif_neg hlu]
      refine hb.trans ?_
      have : (u : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : u ≤ M)
      nlinarith

lemma e57_greedy_le {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) :
    natMakespan P (greedySchedule P hm) ≤ m * natMakespan P σ := by
  classical
  have hg : ∀ j, ∀ i', P (greedySchedule P hm j) j ≤ P i' j := by
    intro j
    have := Finset.min'_mem (Finset.univ.filter (fun i : Fin m => ∀ i', P i j ≤ P i' j)) (by
      obtain ⟨i, -, hi⟩ :=
        Finset.univ.exists_min_image (fun i => P i j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      exact ⟨i, by simpa using hi⟩)
    exact (Finset.mem_filter.1 this).2
  have h1 : natMakespan P (greedySchedule P hm) ≤ ∑ j, P (greedySchedule P hm j) j := by
    unfold natMakespan
    apply Finset.sup_le
    intro i _
    unfold natLoad
    calc ∑ j ∈ Finset.univ.filter (fun j => greedySchedule P hm j = i), P i j
        = ∑ j ∈ Finset.univ.filter (fun j => greedySchedule P hm j = i),
            P (greedySchedule P hm j) j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.1 hj).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
  have h2 : ∑ j, P (greedySchedule P hm j) j ≤ ∑ j, P (σ j) j :=
    Finset.sum_le_sum (fun j _ => hg j (σ j))
  have h3 : ∑ j, P (σ j) j = ∑ i, natLoad P σ i := by
    unfold natLoad
    rw [← Finset.sum_fiberwise Finset.univ σ (fun j => P (σ j) j)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  have h4 : ∑ i, natLoad P σ i ≤ ∑ _i : Fin m, natMakespan P σ := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.le_sup (f := fun i => natLoad P σ i) (Finset.mem_univ i)
  have h5 : ∑ _i : Fin m, natMakespan P σ = m * natMakespan P σ := by simp
  omega

theorem lemma1_core {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (ρ : ℝ) (D : DecisionProcedure m n) (hD : IsRelaxedDecisionProcedure P ρ D)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    makespan (realTimes P) (binarySearch P hm D) ≤ ρ * makespan (realTimes P) σopt := by
  set M := natMakespan P σopt with hM
  have hMeq : makespan (realTimes P) σopt = (M : ℝ) := e57_makespan_eq P σopt
  have hsome : ∀ d σ, D d = some σ → (natMakespan P σ : ℝ) ≤ ρ * (d : ℝ) := by
    intro d σ h
    have := (hD d).1 σ h
    rwa [e57_makespan_eq] at this
  have hnone : ∀ d, D d = none → d < M := by
    intro d hd
    have := (hD d).2 hd σopt
    rw [hMeq] at this
    exact_mod_cast this
  have hDM : ∀ d, M ≤ d → ∃ σ, D d = some σ := by
    intro d hd
    rcases h : D d with _ | σ
    · exact absurd (hnone d h) (by omega)
    · exact ⟨σ, rfl⟩
  have hρ : 0 ≤ ρ := by
    obtain ⟨σ, hσ⟩ := hDM (M + 1) (by omega)
    have h1 := hsome _ σ hσ
    have h2 : (0 : ℝ) ≤ natMakespan P σ := by positivity
    by_contra hneg
    push_neg at hneg
    have : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  set T := natMakespan P (greedySchedule P hm) with hT
  have hTM : T ≤ m * M := e57_greedy_le hm P σopt
  have hinit : (T : ℝ) ≤ ρ * (T : ℝ) := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0]; simp
    · have hMpos : 0 < M := by
        rcases Nat.eq_zero_or_pos M with h | h
        · rw [h] at hTM; omega
        · exact h
      obtain ⟨σ, hσ⟩ := hDM M le_rfl
      have h1 := hsome _ σ hσ
      have h2 := hopt σ
      rw [hMeq, e57_makespan_eq] at h2
      have h3 : (M : ℝ) ≤ ρ * M := le_trans h2 h1
      have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
      have hρ1 : 1 ≤ ρ := by
        by_contra hlt
        push_neg at hlt
        nlinarith
      have : (0 : ℝ) ≤ T := by positivity
      nlinarith
  rw [hMeq, e57_makespan_eq]
  unfold binarySearch
  apply e57_loop P ρ hρ D M hsome hnone
  · exact le_refl _
  · rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hm)]
    have h2 : (T : ℚ) ≤ ((m * M : ℕ) : ℚ) := by exact_mod_cast hTM
    push_cast at h2
    linarith
  · exact hinit

theorem lpproc_core {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (D : DecisionProcedure m n) (hD : IsLPRoundingProcedure P V D) :
    IsRelaxedDecisionProcedure P 2 D := by
  intro d
  refine ⟨?_, ?_⟩
  · intro σ hσ
    obtain ⟨x, _, _, hip⟩ := (hD d).2 σ hσ
    apply Real.iSup_le _ (by positivity)
    intro i
    have := hip.2 i
    linarith
  · intro hnone τ
    have hVn : V d = none := ((hD d).1).1 hnone
    have hemp := (hV d).2 hVn
    by_contra hle
    push_neg at hle
    have := yes_core P (d : ℝ) τ hle
    rw [hemp] at this
    exact this

theorem theorem2_core {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    (∃ D : DecisionProcedure m n, IsLPRoundingProcedure P V D) ∧
      ∀ D : DecisionProcedure m n, IsLPRoundingProcedure P V D →
        makespan (realTimes P) (binarySearch P hm D) ≤ 2 * makespan (realTimes P) σopt := by
  refine ⟨?_, fun D hD => lemma1_core hm P hP 2 D (lpproc_core P V hV D hD) σopt hopt⟩
  have key : ∀ d : ℕ, ∃ o : Option (Fin n → Fin m), (o = none ↔ V d = none) ∧
      ∀ σ, o = some σ → ∃ x, V d = some x ∧ SupportedOn x σ ∧
        IPFeasible P (fun _ => (d : ℝ)) d σ := by
    intro d
    rcases hVd : V d with _ | x
    · exact ⟨none, ⟨fun _ => rfl, fun _ => rfl⟩, fun σ hσ => by simp at hσ⟩
    · obtain ⟨σ, hs, hi⟩ := UnrelatedSched.TwoApprox.theorem_1 P (fun _ => (d : ℝ)) (d : ℝ) (by positivity) x
        ((hV d).1 x hVd)
      exact ⟨some σ, ⟨by simp, by simp⟩, fun σ' hσ' => by
        obtain rfl : σ = σ' := by simpa using hσ'
        exact ⟨x, rfl, hs, hi⟩⟩
  choose D hD using key
  exact ⟨D, fun d => ⟨(hD d).1, (hD d).2⟩⟩

end

section
open MatousekLP.Scheduling
open UnrelatedSched.TwoApprox

theorem solution {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    (∃ D : DecisionProcedure m n, IsLPRoundingProcedure P V D) ∧
      ∀ D : DecisionProcedure m n, IsLPRoundingProcedure P V D →
        makespan (realTimes P) (binarySearch P hm D) ≤ 2 * makespan (realTimes P) σopt := by
  exact theorem2_core hm P hP V hV σopt hopt

end
