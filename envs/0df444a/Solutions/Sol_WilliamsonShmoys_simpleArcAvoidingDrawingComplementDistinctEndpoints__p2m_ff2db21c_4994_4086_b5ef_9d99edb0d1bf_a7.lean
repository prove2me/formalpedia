-- Prove2me | solution 1 for WilliamsonShmoys.simpleArcAvoidingDrawingComplementDistinctEndpoints__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:18:58.768173+00:00
-- url     : https://prove2.me/submissions/4c9008a6-744e-49dc-a1ed-66506eb9d118
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_injective_subpath_in_euclidean_plane__p2m_c87c3c00_b1b8_447c_b699_4692a3a46853_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (u v : V) (huv : u < v)
    (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = p u ∧ delta 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, delta t ≠ arc x y s) := by
  have huv_ne : u ≠ v := by
    intro h
    exact (ne_of_lt huv) h
  have hpuv_ne : p u ≠ p v := fun h => huv_ne (hp h)
  have hend_ne : gamma 0 ≠ gamma 1 := by
    intro h
    apply hpuv_ne
    exact hzero.symm.trans (h.trans hone)
  let shifted : ℝ → ℝ × ℝ := fun t => gamma t - gamma 0
  have hshift_cont : ContinuousOn shifted (Set.Icc 0 1) := by
    dsimp [shifted]
    exact hcont.sub continuousOn_const
  have hshift_zero : shifted 0 = 0 := by
    simp [shifted]
  have hshift_end_ne : shifted 1 ≠ shifted 0 := by
    intro h
    have hz : gamma 1 - gamma 0 = 0 := by
      simpa [shifted] using h
    exact hend_ne (sub_eq_zero.mp hz).symm
  obtain ⟨delta', hdelta_cont, hdelta_inj, hdelta_zero, hdelta_one, hdelta_range⟩ :=
    WilliamsonShmoys.exists_injective_subpath_in_euclidean_plane__p2m_c87c3c00_b1b8_447c_b699_4692a3a46853_a3
      shifted hshift_cont hshift_zero hshift_end_ne
  let delta : ℝ → ℝ × ℝ := fun t => delta' t + gamma 0
  have hdelta_continuous : ContinuousOn delta (Set.Icc 0 1) := by
    dsimp [delta]
    exact hdelta_cont.add continuousOn_const
  have hdelta_injective : Set.InjOn delta (Set.Icc 0 1) := by
    intro x hx y hy hxy
    apply hdelta_inj hx hy
    exact add_right_cancel hxy
  have hdelta_at_zero : delta 0 = p u := by
    dsimp [delta]
    rw [hdelta_zero]
    simp [shifted, hzero]
  have hdelta_at_one : delta 1 = p v := by
    dsimp [delta]
    rw [hdelta_one]
    simp [shifted, hone]
  refine ⟨delta, hdelta_continuous, hdelta_injective, hdelta_at_zero, hdelta_at_one, ?_, ?_⟩
  · intro t ht w hbad
    obtain ⟨s, hs, hEq⟩ := hdelta_range t ht
    have hEq' : delta t = gamma s := by
      dsimp [delta]
      rw [hEq]
      simp [shifted]
    exact havoidV s hs w (hEq'.symm.trans hbad)
  · intro t ht x y hxy hAdj s hs hbad
    obtain ⟨r, hr, hEq⟩ := hdelta_range t ht
    have hEq' : delta t = gamma r := by
      dsimp [delta]
      rw [hEq]
      simp [shifted]
    exact havoidE r hr x y hxy hAdj s hs (hEq'.symm.trans hbad)