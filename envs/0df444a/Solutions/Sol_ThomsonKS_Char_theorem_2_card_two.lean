-- Prove2me | solution 1 for ThomsonKS.Char.theorem_2_card_two
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:46:47.074255+00:00
-- url     : https://prove2.me/submissions/cb2b9aa4-b39a-4eb6-bb55-58791aa6d27f

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting
import Theorems.Thm_ThomsonKS_Char_theorem_2

open ThomsonKS.Char

theorem solution (F : Solution) (hF : IsSolution F) (hW : WPO F) (hA : An F)
    (hI : SInv F) (hM : Mon F) (P : Finset ℕ) (hP : P.card = 2) (S : Set (P → ℝ))
    (hS : S ∈ DivProb P) : KS P S ≤ F P S :=
  theorem_2 F hF hW hA hI hM P S hS
