-- Prove2me | solution 1 for ReentrantScheduling.FBFS.theorem1_fbfs_stable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:18:47.544822+00:00
-- url     : https://prove2.me/submissions/e4cdf3eb-a381-40c8-82d1-286b3d96ba78

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants
import Theorems.Thm_ReentrantScheduling_FBFS_busy_period_bound
import Theorems.Thm_ReentrantScheduling_FBFS_eventual_delay_bound

open ReentrantScheduling.FBFS Finset

theorem solution
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    R.Stable := by
  obtain ⟨Tb, hTb⟩ := busy_period_bound L lam γ hlam hγ hload R hR harr
  obtain ⟨T, hT⟩ := eventual_delay_bound L lam γ hlam hγ hload R hR harr
  -- Step 1: a part that has arrived at a buffer is eventually served there.
  have fin_start : ∀ (p : R.Part) (k : Fin L.l) (a : ℝ), R.entry p ≤ k →
      R.arrive p k = (a : WithTop ℝ) → ∃ s : ℝ, R.start p k = (s : WithTop ℝ) := by
    intro p k a hpk ha
    cases hs : R.start p k with
    | coe s => exact ⟨s, rfl⟩
    | top =>
      exfalso
      set T₁ := max a (Tb k + 1)
      have h := hTb k T₁ (T₁ + |L.Gamma lam γ k| + 1)
        (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (by linarith [abs_nonneg (L.Gamma lam γ k)])
        (fun t h1 _ => ⟨p, k, rfl, le_refl _, hpk, by
          rw [ha]; exact_mod_cast le_trans (le_max_left _ _) h1, by rw [hs]; exact WithTop.coe_lt_top t⟩)
      linarith [le_abs_self (L.Gamma lam γ k)]
  -- Step 2: by induction along the route, every service start is finite.
  have fin_all : ∀ (p : R.Part) (k : ℕ) (hk : k < L.l), R.entry p ≤ ⟨k, hk⟩ →
      ∃ s : ℝ, R.start p ⟨k, hk⟩ = (s : WithTop ℝ) := by
    intro p k
    induction k with
    | zero =>
      intro hk hpk
      have he : (⟨0, hk⟩ : Fin L.l) = R.entry p := le_antisymm (Fin.mk_le_mk.mpr (Nat.zero_le _)) hpk
      exact fin_start p _ (R.α p) hpk (by unfold Run.arrive; rw [if_pos he])
    | succ k ih =>
      intro hk hpk
      by_cases he : (⟨k + 1, hk⟩ : Fin L.l) = R.entry p
      · exact fin_start p _ (R.α p) hpk (by unfold Run.arrive; rw [if_pos he])
      · have hlt : R.entry p < ⟨k + 1, hk⟩ := lt_of_le_of_ne hpk (Ne.symm he)
        have hpk' : R.entry p ≤ ⟨k, by omega⟩ := by
          rw [Fin.lt_def] at hlt; rw [Fin.le_def]; simp only at hlt ⊢; omega
        obtain ⟨s, hs⟩ := ih (by omega) hpk'
        refine fin_start p _ (s + L.τ ⟨k, by omega⟩) hpk ?_
        unfold Run.arrive
        rw [if_neg he, if_pos hlt]
        simp only [Nat.add_sub_cancel]
        rw [hs, WithTop.coe_add]
  -- Step 3: every exit time is finite.
  have fin_exit : ∀ p : R.Part, ∃ e : ℝ, R.exit p = (e : WithTop ℝ) := by
    intro p
    obtain ⟨s, hs⟩ := fin_all p (L.l - 1) (by have := L.l_pos; omega)
      (by rw [Fin.le_def]; simp only; have := (R.entry p).isLt; omega)
    exact ⟨s + L.τ ⟨L.l - 1, by have := L.l_pos; omega⟩, by
      unfold Run.exit; rw [hs, WithTop.coe_add]⟩
  choose e he using fin_exit
  -- Step 4: the finitely many parts released by `max T 0` have bounded delays.
  set T0 := max T 0
  set S := (R.α_finite T0).toFinset
  set D := ∑ j : Fin L.l, (L.Gamma lam γ j + L.τ j)
  refine ⟨|D| + ∑ p ∈ S, |e p - R.α p|, by positivity, fun p => ?_⟩
  have hS0 : 0 ≤ ∑ p ∈ S, |e p - R.α p| := sum_nonneg fun _ _ => abs_nonneg _
  by_cases hp : R.α p ≤ T0
  · have hmem : p ∈ S := by simp [S, hp]
    have h1 : |e p - R.α p| ≤ ∑ q ∈ S, |e q - R.α q| :=
      single_le_sum (f := fun q => |e q - R.α q|) (fun _ _ => abs_nonneg _) hmem
    rw [he p]
    have : e p ≤ R.α p + (|D| + ∑ q ∈ S, |e q - R.α q|) := by
      linarith [le_abs_self (e p - R.α p), abs_nonneg D]
    exact_mod_cast this
  · push Not at hp
    have hni : ¬ R.initial p := by
      intro hi; rw [R.α_initial p hi] at hp; linarith [le_max_right T 0]
    have h := hT p hni (lt_of_le_of_lt (le_max_left _ _) hp)
    refine le_trans h ?_
    have : R.α p + D ≤ R.α p + (|D| + ∑ q ∈ S, |e q - R.α q|) := by
      linarith [le_abs_self D]
    exact_mod_cast this
