-- Prove2me | solution 1 for ReliableFacilityLoc.RRSP.split_relaxes_rsp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:18:12.591253+00:00
-- url     : https://prove2.me/submissions/1af157c3-94af-4646-a186-bb831bf737d0

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_Split

set_option autoImplicit false
open Finset ReliableFacilityLoc.RRSP

theorem solution {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsRSPFeasible q Y P W) :
    IsSplitFeasible q Y Y P W ∧
      splitObjective lam d phi mu Y W = rspObjective lam d phi mu Y W := by
  obtain ⟨hL, hP⟩ := h
  refine ⟨⟨hL, hL, hP, fun r => rfl⟩, ?_⟩
  unfold splitObjective rspObjective
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hYg : ∀ j s, 0 ≤ Y j s := fun j s => by rcases hL.binary j s with h | h <;> rw [h] <;> norm_num
  have hY0 : ∀ j, 0 ≤ Y j r := fun j => hYg j r
  have key : ∀ j k, Y j r * W k r = if j = k then W j r else 0 := by
    intro j k
    by_cases hW : W k r = 0
    · by_cases hjk : j = k
      · subst hjk; simp [hW]
      · simp [hW, hjk]
    · have hWpos : 0 < W k r := lt_of_le_of_ne (hP.w_nonneg k r) (Ne.symm hW)
      have hYk : Y k r = 1 := by
        rcases hL.binary k r with h | h
        · have := hP.w_le_z k r
          rw [h] at this
          linarith
        · exact h
      by_cases hjk : j = k
      · subst hjk; simp [hYk]
      · have hYj : Y j r = 0 := by
          have hsum := hL.level_one r
          have h2 : ∑ x ∈ ({j, k} : Finset (Fin (J + 1))), Y x r ≤ ∑ x, Y x r :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hY0 x)
          rw [Finset.sum_pair hjk, hYk] at h2
          have h3 : 0 ≤ ∑ s ∈ Iio r, Y (Fin.last J) s :=
            Finset.sum_nonneg (fun s _ => hYg _ s)
          linarith [hY0 j]
        simp [hYj, hjk]
  rw [Finset.sum_mul_sum]
  have : ∀ j, ∑ k, (lam * ReliableFacilityLoc.Supermod.dExt d phi j * Y j r) * W k r =
      lam * ReliableFacilityLoc.Supermod.dExt d phi j * W j r := by
    intro j
    have e : ∀ k, (lam * ReliableFacilityLoc.Supermod.dExt d phi j * Y j r) * W k r =
        lam * ReliableFacilityLoc.Supermod.dExt d phi j * (if j = k then W j r else 0) := by
      intro k; rw [← key j k]; ring
    simp_rw [e]
    rw [← Finset.mul_sum]
    simp
  exact Finset.sum_congr rfl (fun j _ => this j)
