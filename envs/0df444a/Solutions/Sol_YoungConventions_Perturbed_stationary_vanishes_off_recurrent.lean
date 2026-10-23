-- Prove2me | solution 1 for YoungConventions.Perturbed.stationary_vanishes_off_recurrent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:47:58.113634+00:00
-- url     : https://prove2.me/submissions/db6e6a26-e95a-4bf0-8dbc-48b018cd8a00

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain



namespace YoungConventions.Perturbed

open Finset in
theorem stat_vanish_core {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (ν : X → ℝ) (hν : IsStationaryDist A ν) (z : X) (hz : ¬ IsRecurrentState A z) :
    ν z = 0 := by
  classical
  obtain ⟨hν0, -, hνA⟩ := hν
  have hpowS : ∀ n : ℕ, A ^ n ∈ Matrix.rowStochastic ℝ X := fun n => pow_mem hA n
  have hnn : ∀ n : ℕ, ∀ i j, 0 ≤ (A ^ n) i j := fun n =>
    (Matrix.mem_rowStochastic_iff_sum.mp (hpowS n)).1
  have hvec : Matrix.vecMul ν A = ν := by
    funext y
    simp only [Matrix.vecMul, dotProduct]
    exact hνA y
  have hvecn : ∀ n : ℕ, Matrix.vecMul ν (A ^ n) = ν := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hvec]
  have hstat : ∀ n : ℕ, ∀ y, ∑ x, ν x * (A ^ n) x y = ν y := by
    intro n y
    have := congrFun (hvecn n) y
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [IsRecurrentState, not_forall] at hz
  obtain ⟨y, ⟨n, hn⟩, hyz⟩ := hz
  set B := A ^ n with hB
  have hBrow : ∀ i, ∑ j, B i j = 1 := (Matrix.mem_rowStochastic_iff_sum.mp (hpowS n)).2
  let S := univ.filter (fun w => ¬ Reaches A w z)
  have hclosed : ∀ w u, ¬ Reaches A w z → 0 < B w u → ¬ Reaches A u z := by
    rintro w u hw hwu ⟨m, hm⟩
    apply hw
    refine ⟨n + m, ?_⟩
    rw [pow_add, Matrix.mul_apply]
    have : B w u * (A ^ m) u z ≤ ∑ k, (A ^ n) w k * (A ^ m) k z := by
      apply Finset.single_le_sum (f := fun k => (A ^ n) w k * (A ^ m) k z)
        (fun k _ => mul_nonneg (hnn n w k) (hnn m k z)) (mem_univ u)
    have := mul_pos hwu hm
    linarith
  let s : X → ℝ := fun w => ∑ u ∈ S, B w u
  have hs1 : ∀ w ∈ S, s w = 1 := by
    intro w hw
    have hw' : ¬ Reaches A w z := (mem_filter.mp hw).2
    rw [← hBrow w, ← Finset.sum_filter_add_sum_filter_not univ (fun u => ¬ Reaches A u z)]
    have : ∑ u ∈ univ.filter (fun u => ¬ ¬ Reaches A u z), B w u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hu' : Reaches A u z := not_not.mp (mem_filter.mp hu).2
      by_contra hne
      have hpos : 0 < B w u := lt_of_le_of_ne (hnn n w u) (Ne.symm hne)
      exact hclosed w u hw' hpos hu'
    rw [this, add_zero]
  have hs0 : ∀ w, 0 ≤ s w := fun w => Finset.sum_nonneg (fun u _ => hnn n w u)
  have h1 : ∑ u ∈ S, ν u = ∑ w, ν w * s w := by
    calc ∑ u ∈ S, ν u = ∑ u ∈ S, ∑ w, ν w * B w u := by
          apply Finset.sum_congr rfl; intro u _; exact (hstat n u).symm
      _ = ∑ w, ∑ u ∈ S, ν w * B w u := Finset.sum_comm
      _ = ∑ w, ν w * s w := by
          apply Finset.sum_congr rfl; intro w _; simp only [s, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun w => ¬ Reaches A w z)] at h1
  have h2 : ∑ w ∈ univ.filter (fun w => ¬ Reaches A w z), ν w * s w = ∑ u ∈ S, ν u := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hs1 w hw, mul_one]
  have h3 : ∑ w ∈ univ.filter (fun w => ¬ ¬ Reaches A w z), ν w * s w = 0 := by
    linarith [h1, h2]
  have hzmem : z ∈ univ.filter (fun w => ¬ ¬ Reaches A w z) := by
    rw [mem_filter]
    refine ⟨mem_univ _, not_not.mpr ⟨0, by simp⟩⟩
  have hz0 := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_nonneg (hν0 w) (hs0 w))).mp h3 z hzmem
  have hyS : y ∈ S := mem_filter.mpr ⟨mem_univ _, hyz⟩
  have hszpos : 0 < s z := by
    have : B z y ≤ s z := Finset.single_le_sum (f := fun u => B z u) (fun u _ => hnn n z u) hyS
    linarith
  rcases mul_eq_zero.mp hz0 with h | h
  · exact h
  · linarith

end YoungConventions.Perturbed

open YoungConventions.Perturbed


theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (ν : X → ℝ) (hν : IsStationaryDist A ν) (z : X) (hz : ¬ IsRecurrentState A z) :
    ν z = 0 := by
  exact stat_vanish_core A hA ν hν z hz
