-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.zStep_eq_reductionCost
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:14:19.362221+00:00
-- url     : https://prove2.me/submissions/48f59bfa-afb6-444a-a13e-e6bb2699a28e

import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsFastForwardRun
import Mathlib.Tactic
set_option autoImplicit false
open ScenarioReduction.ForwardSelection Finset

private theorem sel_succ {N : ℕ} (u : ℕ → Fin N) (i : ℕ) :
    sel u (i+1) = insert (u (i+1)) (sel u i) := by
  ext v
  simp only [sel, mem_image, mem_Icc, mem_insert]
  constructor
  · rintro ⟨j,⟨hj1,hji⟩,hjv⟩
    by_cases he : j=i+1
    · left
      simpa [he] using hjv.symm
    · right
      exact ⟨j,⟨hj1,by omega⟩,hjv⟩
  · rintro (rfl | ⟨j,⟨hj1,hji⟩,hjv⟩)
    · exact ⟨i+1,⟨by omega,le_rfl⟩,rfl⟩
    · exact ⟨j,⟨hj1,by omega⟩,hjv⟩

private theorem cstep_inf {N : ℕ} (c : Fin N → Fin N → ℝ) (u : ℕ → Fin N)
    (i : ℕ) (k v : Fin N) : cStep c u (i+1) k v =
      (insert v (sel u i)).inf' (insert_nonempty _ _) (fun j => c k j) := by
  induction i generalizing v with
  | zero => simp [cStep, sel]
  | succ i ih =>
    rw [cStep, ih, ih, ← Finset.inf'_union (insert_nonempty v (sel u i)) (insert_nonempty (u (i+1)) (sel u i))]
    have he : insert v (sel u i) ∪ insert (u (i+1)) (sel u i) = insert v (sel u (i+1)) := by
      rw [sel_succ]
      ext j
      simp only [mem_union, mem_insert]
      tauto
    simp only [he]

private theorem kept_eq {N : ℕ} (u : ℕ → Fin N) (i : ℕ) (v : Fin N) :
    ((Jstep u i).erase v)ᶜ = insert v (sel u i) := by
  ext j
  simp [Jstep]

private theorem cstep_cost {N : ℕ} (c : Fin N → Fin N → ℝ) (u : ℕ → Fin N)
    (i : ℕ) (hi : 1 ≤ i) (v k : Fin N) :
    cStep c u i k v = ((Jstep u (i-1)).erase v)ᶜ.inf' (compl_erase_nonempty _ _) (fun j => c k j) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, kept_eq] using cstep_inf c u j k v

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (u : ℕ → Fin N) (i : ℕ) (hi : 1 ≤ i) (v : Fin N) (hv : v ∈ Jstep u (i - 1)) :
    zStep (scenCost h ω₀ ω) p u i v =
      reductionCost (scenCost h ω₀ ω) p ((Jstep u (i - 1)).erase v)
        (compl_erase_nonempty _ _) := by
  unfold zStep reductionCost
  apply sum_congr rfl
  intro k hk
  rw [cstep_cost _ u i hi v k]
