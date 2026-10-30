-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_path_to_injective_curve__p2m_635a1d24_9162_4bc8_8f51_e7db8e0ee893_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:21.560785+00:00
-- url     : https://prove2.me/submissions/f66b4b99-68ac-4631-947c-ee80307672af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (hp : Function.Injective p)
    {u v : V} (huv : u < v) (γ : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hzero : γ 0 = p u) (hone : γ 1 = p v)
    (hvertices : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ t ≠ p w)
    (hedges : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, γ t ≠ arc x y s) :
    ∃ γ' : ℝ → ℝ × ℝ,
      ContinuousOn γ' (Set.Icc 0 1) ∧ Set.InjOn γ' (Set.Icc 0 1) ∧
      γ' 0 = p u ∧ γ' 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, γ' t ≠ p w) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
        ∀ s ∈ Set.Icc 0 1, γ' t ≠ arc x y s) := by
  have hne : γ 0 ≠ γ 1 := by
    intro h
    have huvEq : u = v := hp (hzero.symm.trans (h.trans hone))
    exact (ne_of_lt huv) huvEq
  obtain ⟨γ', hγ'cont, hγ'inj, hγ'0, hγ'1, hγ'sub⟩ :=
    WilliamsonShmoys.exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2
      γ hcont hne
  refine ⟨γ', hγ'cont, hγ'inj, hγ'0.trans hzero, hγ'1.trans hone, ?_, ?_⟩
  · intro t ht w
    obtain ⟨s, hs, hst⟩ := hγ'sub t (Set.Ioo_subset_Icc_self ht)
    have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      have hEq : γ' t = γ' 0 := hst.symm.trans hγ'0.symm
      have htEq : t = 0 := hγ'inj (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_trans ht.2.le le_rfl⟩)
        (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) hEq
      exact (ne_of_gt ht.1) htEq
    have hs1 : s ≠ 1 := by
      intro hs1
      subst s
      have hEq : γ' t = γ' 1 := hst.symm.trans hγ'1.symm
      have htEq : t = 1 := hγ'inj (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_trans ht.2.le le_rfl⟩)
        (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩) hEq
      exact (ne_of_lt ht.2) htEq
    intro hEq
    exact hvertices s (Set.mem_Ioo.mpr ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),
      lt_of_le_of_ne hs.2 hs1⟩) w (hst.trans hEq)
  · intro t ht x y hxy hadj s hs
    obtain ⟨r, hr, hrt⟩ := hγ'sub t (Set.Ioo_subset_Icc_self ht)
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      have hEq : γ' t = γ' 0 := hrt.symm.trans hγ'0.symm
      have htEq : t = 0 := hγ'inj (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_trans ht.2.le le_rfl⟩)
        (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) hEq
      exact (ne_of_gt ht.1) htEq
    have hr1 : r ≠ 1 := by
      intro hr1
      subst r
      have hEq : γ' t = γ' 1 := hrt.symm.trans hγ'1.symm
      have htEq : t = 1 := hγ'inj (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_trans ht.2.le le_rfl⟩)
        (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩) hEq
      exact (ne_of_lt ht.2) htEq
    intro hEq
    exact hedges r (Set.mem_Ioo.mpr ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),
      lt_of_le_of_ne hr.2 hr1⟩) x y hxy hadj s hs (hrt.trans hEq)