-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.cStep_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:14:18.524844+00:00
-- url     : https://prove2.me/submissions/74cc3e42-b182-4379-b67f-657d030272cb

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
    (ω : Fin N → E) (u : ℕ → Fin N) (i : ℕ) (hi : 1 ≤ i) (v : Fin N)
    (hv : v ∈ Jstep u (i - 1)) (k : Fin N) :
    cStep (scenCost h ω₀ ω) u i k v =
      ((Jstep u (i - 1)).erase v)ᶜ.inf' (compl_erase_nonempty _ _)
        (fun j => scenCost h ω₀ ω k j) := cstep_cost _ u i hi v k
