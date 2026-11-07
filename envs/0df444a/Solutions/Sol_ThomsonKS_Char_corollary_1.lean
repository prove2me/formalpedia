-- Prove2me | solution 1 for ThomsonKS.Char.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:28:17.949226+00:00
-- url     : https://prove2.me/submissions/01aab01d-d50a-499d-b9df-72ea76921f55

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting
import Theorems.Thm_ThomsonKS_Char_theorem_1
import Theorems.Thm_ThomsonKS_Char_theorem_2

open ThomsonKS.Char

theorem solution (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) : ∀ P : Finset ℕ, ∀ S ∈ DivProbTilde P, F P S = KS P S := by
  intro P S hS
  obtain ⟨hK, hKW, -⟩ := theorem_1
  have hge := theorem_2 F hF hW hA hI hM P S hS.1
  by_contra hne
  obtain ⟨z, hz, hzlt⟩ := hS.2 (KS P S) (hK P S hS.1) (F P S) (hF P S hS.1) ⟨hge, Ne.symm hne⟩
  exact hKW P S hS.1 z (fun i => hS.1.2.1 z hz i) hzlt hz
