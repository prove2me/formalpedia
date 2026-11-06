-- Prove2me | solution 1 for ReliableFacilityLoc.Scenario.proposition1_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:37:30.633184+00:00
-- url     : https://prove2.me/submissions/94b37fbc-a900-418e-82e5-ec0c867ad20e

import Theorems.Thm_ReliableFacilityLoc_Scenario_rufl_to_ssp
import Theorems.Thm_ReliableFacilityLoc_Scenario_ssp_nearest_normalization
import Theorems.Thm_ReliableFacilityLoc_Scenario_ssp_to_rufl

open Finset ReliableFacilityLoc.Scenario

namespace RFL1Goal

open Classical

noncomputable def toR (b : Bool) : ℝ := if b = true then 1 else 0

lemma toR_decide {x : ℝ} (h : x = 0 ∨ x = 1) : toR (decide (x = 1)) = x := by
  rcases h with h | h <;> simp [toR, h]

/-- (SSP) has an optimal solution: its feasible set is finite (all variables are binary) and
nonempty (open nothing, serve every customer by the emergency facility). -/
lemma ssp_exists_opt {I J R : ℕ} (D : Instance I J R) :
    ∃ (X : Fin J → ℝ) (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ), D.IsSSPOptimal X Y := by
  let toX : (Fin J → Bool) → Fin J → ℝ := fun b j => toR (b j)
  let toY : (Fin I → Fin (J + 1) → FailureScenario J → Bool) →
      Fin I → Fin (J + 1) → FailureScenario J → ℝ := fun b i j ω => toR (b i j ω)
  let T := (univ : Finset ((Fin J → Bool) × (Fin I → Fin (J + 1) → FailureScenario J → Bool))).filter
    (fun b => D.IsSSPFeasible (toX b.1) (toY b.2))
  have hne : T.Nonempty := by
    refine ⟨(fun _ => false, fun _ j _ => decide (j = Fin.last J)), ?_⟩
    simp only [T, mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i ω
      simp only [toY, toR]
      rw [Finset.sum_eq_single (Fin.last J)]
      · simp
      · intro b _ hb; simp [hb]
      · intro hh; exact absurd (mem_univ _) hh
    · intro i j ω
      simp [toY, toX, toR, Fin.castSucc_ne_last]
    · intro j; simp [toX, toR]
    · intro i j ω; simp only [toY, toR]; split_ifs <;> simp
  obtain ⟨b, hbT, hmin⟩ := T.exists_min_image (fun b => D.sspObjective (toX b.1) (toY b.2)) hne
  refine ⟨toX b.1, toY b.2, (mem_filter.1 hbT).2, fun X' Y' hf => ?_⟩
  let b' : (Fin J → Bool) × (Fin I → Fin (J + 1) → FailureScenario J → Bool) :=
    (fun j => decide (X' j = 1), fun i j ω => decide (Y' i j ω = 1))
  have hX : toX b'.1 = X' := funext fun j => toR_decide (hf.X_binary j)
  have hY : toY b'.2 = Y' := funext fun i => funext fun j => funext fun ω =>
    toR_decide (hf.Y_binary i j ω)
  have hb' : b' ∈ T := by
    simp only [T, mem_filter, mem_univ, true_and]
    rw [hX, hY]; exact hf
  have := hmin b' hb'
  rw [hX, hY] at this
  exact this

end RFL1Goal

theorem solution {I J : ℕ} (D : Instance I J J) :
    (∃ (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ), D.IsRUFLOptimal X Y P) ∧
    (∃ (X : Fin J → ℝ) (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ), D.IsSSPOptimal X Y) ∧
    ∀ (X : Fin J → ℝ) (Y P : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ) (X' : Fin J → ℝ)
      (Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ),
      D.IsRUFLOptimal X Y P → D.IsSSPOptimal X' Y' →
        D.ruflObjective X Y P = D.sspObjective X' Y' := by
  obtain ⟨X0, Y0, hopt0⟩ := RFL1Goal.ssp_exists_opt D
  obtain ⟨Y1, hopt1, hnear⟩ := ssp_nearest_normalization D X0 Y0 hopt0
  obtain ⟨Y2, P2, hfeas2, hobj2⟩ := ssp_to_rufl D X0 Y1 hopt1.1 hnear
  -- every RUFL-feasible solution costs at least the SSP optimum
  have hlb : ∀ X Y P, D.IsRUFLFeasible X Y P → D.sspObjective X0 Y1 ≤ D.ruflObjective X Y P := by
    intro X Y P hf
    obtain ⟨Y', hY'f, hY'o⟩ := rufl_to_ssp D X Y P hf
    rw [← hY'o]
    exact hopt1.2 X Y' hY'f
  have hRopt : D.IsRUFLOptimal X0 Y2 P2 :=
    ⟨hfeas2, fun X' Y' P' hf => by rw [hobj2]; exact hlb X' Y' P' hf⟩
  refine ⟨⟨X0, Y2, P2, hRopt⟩, ⟨X0, Y1, hopt1⟩, ?_⟩
  intro X Y P X' Y' hR hS
  have e1 : D.ruflObjective X Y P = D.sspObjective X0 Y1 := by
    apply le_antisymm
    · rw [← hobj2]; exact hR.2 X0 Y2 P2 hfeas2
    · exact hlb X Y P hR.1
  have e2 : D.sspObjective X' Y' = D.sspObjective X0 Y1 :=
    le_antisymm (hS.2 X0 Y1 hopt1.1) (hopt1.2 X' Y' hS.1)
  rw [e1, e2]
