-- Prove2me | solution 1 for RobustAuction.ROM.rom_feasible_star_dual_lemma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:57:31.771278+00:00
-- url     : https://prove2.me/submissions/f76a8525-ba7d-4f2d-9dc2-659c04cf0599

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

open RobustAuction.ROM

open Finset in
theorem solution {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hROMa : IsROMa U B d) :
    ∀ i, Finset.sum Finset.univ (fun j => d.xs i j * rStar d i j) ≤
      B i + d.θ i * Finset.sum Finset.univ (fun j => d.xs i j * d.ut i i j) := by
  obtain ⟨hz, ⟨hx0, hx1, hxB, hxR⟩, -, hut, ⟨hξ, hη, hθ, hdf⟩, hopt⟩ := hROMa
  set c : Fin n → ℝ := fun i => ∑ j, d.xs i j * d.ut i i j with hc
  -- c i = ∑ xs z
  have hceq : ∀ i, c i = ∑ j, d.xs i j * d.z i j := by
    intro i
    apply le_antisymm ((hut i).2 d.z hz)
    exact hxR (d.ut i) (hut i).1 i
  have hc0 : ∀ i, 0 ≤ c i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hx0 i j) (hU _ (hut i).1 i j)
  -- dual objective ≤ ∑ c
  have hdual : dualObj B d.xs d.ut d.ξ d.η d.θ ≤ ∑ i, c i := by
    have := hopt (fun _ => 0) (fun _ => 0) (fun _ => 1)
      ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => zero_le_one, fun i j => by simp⟩
    simpa [dualObj, hc] using this
  -- termwise slack
  have hT : ∀ i j, 0 ≤ d.xs i j * (rStar d i j - d.z i j) := by
    intro i j
    apply mul_nonneg (hx0 i j)
    have := hdf i j
    simp only [rStar]; nlinarith
  -- ∑ xs r* ≤ dualObj
  have hle : ∑ i, ∑ j, d.xs i j * rStar d i j ≤ dualObj B d.xs d.ut d.ξ d.η d.θ := by
    have e : ∑ i, ∑ j, d.xs i j * rStar d i j =
        ∑ j, d.ξ j * ∑ i, d.xs i j + ∑ i, (d.η i * ∑ j, d.xs i j * d.z i j +
          d.θ i * ∑ j, d.xs i j * d.z i j) := by
      have e1 : ∀ i, ∑ j, d.xs i j * rStar d i j = ∑ j, d.xs i j * d.ξ j +
          (d.η i * ∑ j, d.xs i j * d.z i j + d.θ i * ∑ j, d.xs i j * d.z i j) := by
        intro i
        simp only [rStar, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      have e2 : ∑ i, ∑ j, d.xs i j * d.ξ j = ∑ j, d.ξ j * ∑ i, d.xs i j := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, e2]
    rw [e, dualObj]
    apply add_le_add
    · apply Finset.sum_le_sum; intro j _
      calc d.ξ j * ∑ i, d.xs i j ≤ d.ξ j * 1 := mul_le_mul_of_nonneg_left (hx1 j) (hξ j)
        _ = d.ξ j := mul_one _
    · apply Finset.sum_le_sum; intro i _
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hxB i) (hη i)
      · rw [← hceq i]
  -- hence ∑ i T i ≤ 0
  have hsum : ∑ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) ≤ 0 := by
    have e : ∑ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) =
        ∑ i, ∑ j, d.xs i j * rStar d i j - ∑ i, c i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
      rw [hceq i, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
    rw [e]; linarith
  have hTi : ∀ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) = 0 := by
    intro i
    have h0 : ∀ i, 0 ≤ ∑ j, d.xs i j * (rStar d i j - d.z i j) :=
      fun i => Finset.sum_nonneg fun j _ => hT i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h0 i)).1
      (le_antisymm hsum (Finset.sum_nonneg fun i _ => h0 i)) i (Finset.mem_univ i)
    exact this
  intro i
  have e : ∑ j, d.xs i j * rStar d i j = ∑ j, d.xs i j * d.z i j := by
    have := hTi i
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    rw [← this]; apply Finset.sum_congr rfl; intro j _; ring
  rw [e]
  have := hxB i
  have := mul_nonneg (hθ i) (hc0 i)
  simp only [hc] at this
  linarith
