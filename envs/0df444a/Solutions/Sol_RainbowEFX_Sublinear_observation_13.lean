-- Prove2me | solution 1 for RainbowEFX.Sublinear.observation_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:53:58.171286+00:00
-- url     : https://prove2.me/submissions/3985703f-2350-47f9-861a-036695ec257a

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting
import Theorems.Thm_RainbowEFX_Sublinear_observation_7
import Theorems.Thm_RainbowEFX_Sublinear_observation_11

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hstar : Star ε v X) (src : Fin n → Fin n) (hsrc : IsSourceAssignment v X src)
    (g h : Fin m) (hg : g ∈ LX ε v X d) (hh : h ∈ LX ε v X d) (x : Fin n)
    (hx : GCVertex ε v X d src (h, x)) :
    ∃ y, GCVertex ε v X d src (g, y) ∧ GCAdj ε v X src (g, y) (h, x) := by
  classical
  have hε1 : ε < 1 := by linarith
  have mono : ∀ i (A B : Finset (Fin m)), A ⊆ B → v i A ≤ v i B := by
    intro i A B hAB
    rw [hv.1 i A, hv.1 i B]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hv.2 i {x})
  -- strong envy implies heavy envy
  have sh : ∀ i S, StronglyEnvies ε v X i S → HeavilyEnvies ε v X i S := by
    rintro i S ⟨T, hTS, hT⟩
    unfold HeavilyEnvies at *
    have := mono i T S hTS.subset
    nlinarith
  obtain ⟨-, b, hb, rfl⟩ := hx
  have hgP : g ∈ pool X := (Finset.mem_filter.mp hg).1
  have hs : IsSource v X (src b) := (hsrc b).1
  set S := insert g (X (src b)) with hS
  -- (*) : rule U1 does not apply, so someone strongly envies S
  have hstrong : ∃ i, StronglyEnvies ε v X i S := by
    by_contra hcon
    push_neg at hcon
    exact hstar.2.1 ⟨src b, hs, g, hgP, hcon⟩
  obtain ⟨i0, hi0⟩ := hstrong
  obtain ⟨a, Z, hZ⟩ := (observation_7 v hv ε hε0 hε1 X S).1 ⟨i0, sh _ _ hi0⟩
  have ha : IsMostEnviousAgent ε v X S a := ⟨Z, hZ⟩
  have haS : StronglyEnvies ε v X a S :=
    (observation_7 v hv ε hε0 hε1 X S).2 ⟨i0, hi0⟩ a ha
  have hval : Valuable ε v X g a :=
    observation_11 v hv ε hε0 hε1 X g hgP (src b) hs a (sh _ _ haS)
  exact ⟨src a, ⟨hg, a, hval, rfl⟩, a, b, hval, hb, rfl, rfl, ha⟩
