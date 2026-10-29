-- Prove2me | solution 1 for PochetWolsey.BacklogStartup.no_setup_interval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:22:35.221214+00:00
-- url     : https://prove2.me/submissions/15f43f25-894b-42b6-add2-08db3fd5f2da

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel

open PochetWolsey.BacklogStartup

theorem solution {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (y z : Fin n → ℝ) (h : ExactStartup y0 y z)
    (k t : ℕ) (hk : 1 ≤ k) (hkt : k < t) (ht : t ≤ n) :
    (period y k + ∑ j ∈ Finset.Icc (k + 1) t, period z j) = 0 ↔
      ∀ j ∈ Finset.Icc k t, period y j = 0 := by
  obtain ⟨hyb, hzb, hc⟩ := h
  have nn : ∀ (v : Fin n → ℝ), Binary v → ∀ i, 0 ≤ period v i := by
    intro v hv i
    unfold period
    split_ifs
    · rcases hv ⟨i - 1, by omega⟩ with h | h <;> rw [h] <;> norm_num
    · exact le_refl _
  constructor
  · intro hsum
    have hs0 : 0 ≤ ∑ j ∈ Finset.Icc (k + 1) t, period z j :=
      Finset.sum_nonneg (fun j _ => nn z hzb j)
    have hyk0 := nn y hyb k
    have hyk : period y k = 0 := by linarith
    have hzs : ∑ j ∈ Finset.Icc (k + 1) t, period z j = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => nn z hzb j)] at hzs
    have main : ∀ m, k + m ≤ t → period y (k + m) = 0 := by
      intro m
      induction m with
      | zero => intro _; simpa using hyk
      | succ m ih =>
        intro hm
        have ih' := ih (by omega)
        have hcj := (hc (k + m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
        have hz0 := hzs (k + m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hss : setupState y0 y (k + m + 1 - 1) = 0 := by
          unfold setupState
          rw [if_neg (by omega)]
          simpa using ih'
        rw [hss, hz0] at hcj
        have := nn y hyb (k + m + 1)
        rw [← add_assoc]
        linarith
    intro j hj
    rw [Finset.mem_Icc] at hj
    have := main (j - k) (by omega)
    rwa [show k + (j - k) = j by omega] at this
  · intro hall
    rw [hall k (Finset.mem_Icc.mpr ⟨le_refl _, hkt.le⟩), zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h1 := (hc j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2.1
    have h2 := hall j (Finset.mem_Icc.mpr ⟨by omega, hj.2⟩)
    have h3 := nn z hzb j
    linarith
