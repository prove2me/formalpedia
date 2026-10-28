-- Prove2me | solution 1 for RainbowEFX.Sublinear.observation_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:36:01.212876+00:00
-- url     : https://prove2.me/submissions/7260a3d0-f434-461c-8072-f0a337d6fd9f

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX

open RainbowEFX.Sublinear in
theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (g : Fin m) (hg : g ∈ pool X) (s : Fin n)
    (hs : IsSource v X s) (i : Fin n) (hi : HeavilyEnvies ε v X i (insert g (X s))) :
    Valuable ε v X g i := by
  have hgs : g ∉ X s := by
    intro h
    unfold pool at hg
    rw [Finset.mem_sdiff] at hg
    exact hg.2 (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, h⟩)
  have hadd : v i (insert g (X s)) = v i {g} + v i (X s) := by
    rw [hv.1 i (insert g (X s)), Finset.sum_insert hgs, ← hv.1 i (X s)]
  have hsrc : v i (X s) ≤ v i (X i) := by
    have := hs i
    unfold Envies at this
    exact not_lt.mp this
  have hg0 : 0 ≤ v i {g} := hv.2 i {g}
  unfold HeavilyEnvies at hi
  unfold Valuable
  rw [hadd] at hi
  nlinarith
