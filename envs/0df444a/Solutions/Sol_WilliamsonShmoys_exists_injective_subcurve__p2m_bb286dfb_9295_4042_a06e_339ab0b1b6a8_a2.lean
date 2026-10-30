-- Prove2me | solution 1 for WilliamsonShmoys.exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:36.795992+00:00
-- url     : https://prove2.me/submissions/21ae1a16-d04b-4f14-a054-f2dab870d259
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2
import Theorems.Thm_WilliamsonShmoys_compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1

set_option autoImplicit false

theorem solution
    (γ : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hne : γ 0 ≠ γ 1) :
    ∃ γ' : ℝ → ℝ × ℝ,
      ContinuousOn γ' (Set.Icc 0 1) ∧
      Set.InjOn γ' (Set.Icc 0 1) ∧
      γ' 0 = γ 0 ∧
      γ' 1 = γ 1 ∧
      (∀ t ∈ Set.Icc 0 1, ∃ s ∈ Set.Icc 0 1, γ s = γ' t) := by
  let S : Set (ℝ × ℝ) := γ '' Set.Icc 0 1
  have hS :
      IsCompact S ∧ IsPathConnected S ∧ LocallyConnectedSpace S := by
    simpa [S] using
      WilliamsonShmoys.path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2
        γ hcont
  letI : LocallyConnectedSpace S := hS.2.2
  let a : S := ⟨γ 0, ⟨0, by norm_num, rfl⟩⟩
  let b : S := ⟨γ 1, ⟨1, by norm_num, rfl⟩⟩
  have hab : a ≠ b := by
    intro h
    apply hne
    exact congrArg Subtype.val h
  obtain ⟨γ', hγ'cont, hγ'inj, hγ'0, hγ'1, hγ'range⟩ :=
    WilliamsonShmoys.compact_locally_connected_subtype_has_arc__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
      hS.1 hS.2.1 hS.2.2 a b hab
  refine ⟨γ', hγ'cont, hγ'inj, ?_, ?_, ?_⟩
  · simpa [a] using hγ'0
  · simpa [b] using hγ'1
  · intro t ht
    have hmem : γ' t ∈ γ '' Set.Icc 0 1 := by
      simpa [S] using hγ'range t ht
    rcases hmem with ⟨s, hs, hγs⟩
    exact ⟨s, hs, hγs⟩
