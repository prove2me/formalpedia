-- Prove2me | solution 1 for ReliableFacilityLoc.Scenario.scenario_prob_first_operating
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:41:20.641535+00:00
-- url     : https://prove2.me/submissions/81a71577-8fba-497c-9b23-92e0d4cb8cd2

import Mathlib
import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

set_option autoImplicit false
open Finset ReliableFacilityLoc.Scenario

lemma sfo_sum {J : ℕ} (q : Fin J → ℝ) (t : Fin J → Finset Bool) :
    ∑ ω ∈ Fintype.piFinset t, ∏ j, (if ω j then 1 - q j else q j)
      = ∏ j, ∑ b ∈ t j, (if b then 1 - q j else q j) :=
  (Finset.prod_univ_sum t (fun j b => if b then 1 - q j else q j)).symm

def tSet {J : ℕ} (l : List (Fin J)) (j0 : Fin J) : Fin J → Finset Bool :=
  fun j => if j ∈ l.toFinset then {false} else if j = j0 then {true} else Finset.univ

def tSetL {J : ℕ} (l : List (Fin J)) : Fin J → Finset Bool :=
  fun j => if j ∈ l.toFinset then {false} else Finset.univ

theorem solution {I J R : ℕ} (D : Instance I J R) (l : List (Fin J))
    (hl : l.Nodup) (k : Fin (J + 1)) (hk : ∀ j ∈ l, j.castSucc ≠ k) :
    ∑ ω ∈ univ.filter (fun ω : FailureScenario J => delta ω k = true ∧ ∀ j ∈ l, ω j = false),
        D.scenarioProb ω =
      (1 - D.qExt k) * (l.map D.q).prod := by
  classical
  have hprod : (l.map D.q).prod = ∏ j ∈ l.toFinset, D.q j := (List.prod_toFinset D.q hl).symm
  rw [hprod]
  induction k using Fin.lastCases with
  | last =>
    have hfil : univ.filter (fun ω : FailureScenario J =>
          delta ω (Fin.last J) = true ∧ ∀ j ∈ l, ω j = false)
        = Fintype.piFinset (tSetL l) := by
      ext ω
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, -, hω⟩ j
        by_cases hj : j ∈ l.toFinset
        · simp [tSetL, hj, hω j (List.mem_toFinset.mp hj)]
        · simp [tSetL, hj]
      · intro h
        refine ⟨Finset.mem_univ _, by simp [delta], fun j hj => ?_⟩
        have h' := h j
        have hj' : j ∈ l.toFinset := List.mem_toFinset.mpr hj
        simpa [tSetL, hj'] using h'
    rw [hfil]
    simp only [Instance.scenarioProb]
    rw [sfo_sum]
    have hS : ∀ j : Fin J, ∑ b ∈ tSetL l j, (if b then 1 - D.q j else D.q j)
        = if j ∈ l.toFinset then D.q j else 1 := by
      intro j
      by_cases hj : j ∈ l.toFinset
      · simp [tSetL, hj]
      · simp [tSetL, hj, Fintype.sum_bool]
    simp only [hS]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    simp [Instance.qExt]
  | cast j0 =>
    have hj0 : j0 ∉ l := fun h => hk j0 h rfl
    have hj0' : j0 ∉ l.toFinset := by simpa using hj0
    have hfil : univ.filter (fun ω : FailureScenario J =>
          delta ω j0.castSucc = true ∧ ∀ j ∈ l, ω j = false)
        = Fintype.piFinset (tSet l j0) := by
      ext ω
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, hd, hω⟩ j
        have hd' : ω j0 = true := by simpa [delta] using hd
        by_cases hj : j ∈ l.toFinset
        · simp [tSet, hj, hω j (List.mem_toFinset.mp hj)]
        · by_cases hjj : j = j0
          · subst hjj
            simp [tSet, hj, hd']
          · simp [tSet, hj, hjj]
      · intro h
        refine ⟨Finset.mem_univ _, ?_, fun j hj => ?_⟩
        · have h' := h j0
          simp only [tSet, hj0', if_false, if_true] at h'
          simpa [delta] using h'
        · have h' := h j
          have hj' : j ∈ l.toFinset := List.mem_toFinset.mpr hj
          simpa [tSet, hj'] using h'
    rw [hfil]
    simp only [Instance.scenarioProb]
    rw [sfo_sum]
    have hS : ∀ j : Fin J, ∑ b ∈ tSet l j0 j, (if b then 1 - D.q j else D.q j)
        = (if j ∈ l.toFinset then D.q j else 1) * (if j = j0 then 1 - D.q j0 else 1) := by
      intro j
      by_cases hj : j ∈ l.toFinset
      · have hne : j ≠ j0 := fun h => hj0' (h ▸ hj)
        simp [tSet, hj, hne]
      · by_cases hjj : j = j0
        · subst hjj
          simp [tSet, hj]
        · simp [tSet, hj, hjj, Fintype.sum_bool]
    simp only [hS]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_eq']
    simp [Instance.qExt, mul_comm]
