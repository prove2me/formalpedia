-- Prove2me | solution 1 for SparseNLO.IHT.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:04:42.593182+00:00
-- url     : https://prove2.me/submissions/19fcd7d0-4b3d-4596-b46d-2ec5af198229

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

set_option autoImplicit false
open Filter Topology SparseNLO.IHT

theorem sih_coord {n s : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ projCs n s y) (i : Fin n)
    (hi : SparseNLO.CWOpt.l0 x < s ∨ x i ≠ 0) : x i = y i := by
  set z : EuclideanSpace ℝ (Fin n) := x + EuclideanSpace.single i (y i - x i) with hz
  have hzj : ∀ j, z j = if j = i then y i else x j := by
    intro j
    by_cases h : j = i
    · subst h; simp [hz]
    · simp [hz, h, EuclideanSpace.single_apply]
  have hzC : z ∈ SparseNLO.CWOpt.Cs n s := by
    have hsub : SparseNLO.CWOpt.I1 z ⊆ insert i (SparseNLO.CWOpt.I1 x) := by
      intro j hj
      simp only [SparseNLO.CWOpt.I1, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hzj] at hj
      by_cases h : j = i
      · simp [h]
      · simp only [h, if_false] at hj
        simp [SparseNLO.CWOpt.I1, hj]
    have hcard := Finset.card_le_card hsub
    show SparseNLO.CWOpt.l0 z ≤ s
    have h1 : SparseNLO.CWOpt.l0 z = (SparseNLO.CWOpt.I1 z).card := rfl
    have h2 : SparseNLO.CWOpt.l0 x = (SparseNLO.CWOpt.I1 x).card := rfl
    rcases hi with hi | hi
    · have := Finset.card_insert_le i (SparseNLO.CWOpt.I1 x)
      omega
    · have hmem : i ∈ SparseNLO.CWOpt.I1 x := by simp [SparseNLO.CWOpt.I1, hi]
      rw [Finset.insert_eq_of_mem hmem] at hcard
      have := hx.1
      have h3 : SparseNLO.CWOpt.l0 x ≤ s := this
      omega
  have hle := hx.2 z hzC
  have hsq : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 = ∑ j, (w j) ^ 2 := by
    intro w; rw [EuclideanSpace.norm_sq_eq]; simp
  have h2 : ‖x - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by gcongr
  rw [hsq, hsq] at h2
  have hdiff : ∑ j, ((z - y) j) ^ 2 + (x i - y i) ^ 2 = ∑ j, ((x - y) j) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => ((x - y) j) ^ 2) (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, ((z - y) j) ^ 2 = ∑ j ∈ Finset.univ.erase i, ((x - y) j) ^ 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hzj, hji]
    rw [this]
    have : (z - y) i = 0 := by simp [hzj]
    rw [this]
    simp
  have : (x i - y i) ^ 2 ≤ 0 := by linarith
  have : x i - y i = 0 := by nlinarith [sq_nonneg (x i - y i)]
  linarith

theorem solution {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) (hx : IsLStationary f s L x) :
    SparseNLO.CWOpt.IsBF f s x := by
  obtain ⟨hxC, hxp⟩ := hx
  have key : ∀ i, (SparseNLO.CWOpt.l0 x < s ∨ x i ≠ 0) → gradient f x i = 0 := by
    intro i hi
    have := sih_coord x _ hxp i hi
    have e : (x - (1 / L) • gradient f x) i = x i - (1 / L) * gradient f x i := by simp
    rw [e] at this
    have h2 : (1 / L) * gradient f x i = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by positivity)
    · exact h
  refine ⟨hxC, ?_, ?_⟩
  · intro hlt
    ext i
    simpa using key i (Or.inl hlt)
  · intro _ i hi
    have : x i ≠ 0 := by simpa [SparseNLO.CWOpt.I1] using hi
    exact key i (Or.inr this)
