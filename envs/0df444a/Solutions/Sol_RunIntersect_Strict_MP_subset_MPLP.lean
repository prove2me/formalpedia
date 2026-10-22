-- Prove2me | solution 1 for RunIntersect.Strict.MP_subset_MPLP
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:38:16.38399+00:00
-- url     : https://prove2.me/submissions/94bc39dc-8c14-4630-8641-843a75b87366

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting
set_option autoImplicit false
open RunIntersect.Strict

theorem solution {α : Type*} [Fintype α] [DecidableEq α] (G : RunIntersect.Strict.Hypergraph α) :
    MP G ⊆ MPLP G := by
  have hconv : Convex ℝ (MPLP G) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx1 v hv, hy1 v hv]
    · intro e he
      obtain ⟨a1, a2, a3⟩ := hx2 e he
      obtain ⟨b1, b2, b3⟩ := hy2 e he
      refine ⟨?_, ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have : (e.card : ℝ) = a * e.card + b * e.card := by rw [← add_mul, hab, one_mul]
        nlinarith
      · intro v hv
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [a3 v hv, b3 v hv]
    · intro p hp
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx3 p hp, hy3 p hp]
      ring
  refine convexHull_min ?_ hconv
  intro z hz
  obtain ⟨h01, hprod, hoff⟩ := hz
  refine ⟨?_, ?_, hoff⟩
  · intro v hv
    rcases h01 v hv with h | h <;> rw [h] <;> norm_num
  · intro e he
    have hprod' := hprod e he
    have hesub := G.edge_subset e he
    by_cases hall : ∀ v ∈ e, z (Sum.inl v) = 1
    · have : ∏ v ∈ e, z (Sum.inl v) = 1 := Finset.prod_eq_one hall
      rw [hprod', this]
      have hs : ∑ v ∈ e, z (Sum.inl v) = e.card := by
        rw [Finset.sum_congr rfl hall]; simp
      refine ⟨by norm_num, by rw [hs]; linarith, fun v hv => by rw [hall v hv]⟩
    · push_neg at hall
      obtain ⟨w, hwe, hw⟩ := hall
      have hw0 : z (Sum.inl w) = 0 := by
        rcases h01 w (hesub hwe) with h | h
        · exact h
        · exact absurd h hw
      have hp0 : ∏ v ∈ e, z (Sum.inl v) = 0 := Finset.prod_eq_zero hwe hw0
      rw [hprod', hp0]
      have hle : ∑ v ∈ e, z (Sum.inl v) ≤ e.card - 1 := by
        have h1 : ∑ v ∈ e, z (Sum.inl v) = ∑ v ∈ e.erase w, z (Sum.inl v) := by
          rw [← Finset.add_sum_erase e _ hwe, hw0, zero_add]
        have h2 : ∑ v ∈ e.erase w, z (Sum.inl v) ≤ ∑ v ∈ e.erase w, (1:ℝ) :=
          Finset.sum_le_sum (fun v hv => by
            rcases h01 v (hesub (Finset.mem_of_mem_erase hv)) with h | h <;> rw [h] <;> norm_num)
        have h3 : ∑ v ∈ e.erase w, (1:ℝ) = (e.card : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hwe, nsmul_eq_mul, mul_one]
          have := Finset.card_pos.mpr ⟨w, hwe⟩
          push_cast [Nat.cast_sub this]
          ring
        linarith
      refine ⟨le_refl _, by linarith, fun v hv => ?_⟩
      rcases h01 v (hesub hv) with h | h <;> rw [h] <;> norm_num
