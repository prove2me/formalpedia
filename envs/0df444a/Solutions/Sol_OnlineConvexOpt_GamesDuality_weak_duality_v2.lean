-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.weak_duality_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:33:45.148181+00:00
-- url     : https://prove2.me/submissions/abd8a4a9-af41-447f-a2ef-7f6809dcf671

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

set_option autoImplicit false

open OnlineConvexOpt.GamesDuality in
theorem gd2_rowValue_cont_y {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) :
    Continuous (fun y : Fin m → ℝ => rowValue A x y) := by
  unfold rowValue
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

open OnlineConvexOpt.GamesDuality in
theorem gd2_rowValue_cont_x {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (y : Fin m → ℝ) :
    Continuous (fun x : Fin n → ℝ => rowValue A x y) := by
  unfold rowValue
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem gd2_simplex_nonempty {k : ℕ} (hk : 0 < k) : (stdSimplex ℝ (Fin k)).Nonempty :=
  ⟨Pi.single ⟨0, hk⟩ 1, single_mem_stdSimplex ℝ _⟩

open OnlineConvexOpt.GamesDuality in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ) :
    lambdaC A ≤ lambdaR A := by
  have key : ∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin m),
      sInf ((fun x => rowValue A x y) '' stdSimplex ℝ (Fin n)) ≤
        sSup ((fun y => rowValue A x y) '' stdSimplex ℝ (Fin m)) := by
    intro x hx y hy
    have h1 : sInf ((fun x => rowValue A x y) '' stdSimplex ℝ (Fin n)) ≤ rowValue A x y :=
      csInf_le ((isCompact_stdSimplex ℝ (Fin n)).bddBelow_image
        (gd2_rowValue_cont_x A y).continuousOn) ⟨x, hx, rfl⟩
    have h2 : rowValue A x y ≤ sSup ((fun y => rowValue A x y) '' stdSimplex ℝ (Fin m)) :=
      le_csSup ((isCompact_stdSimplex ℝ (Fin m)).bddAbove_image
        (gd2_rowValue_cont_y A x).continuousOn) ⟨y, hy, rfl⟩
    exact h1.trans h2
  unfold lambdaC lambdaR
  apply le_csInf ((gd2_simplex_nonempty hn).image _)
  rintro _ ⟨x, hx, rfl⟩
  apply csSup_le ((gd2_simplex_nonempty hm).image _)
  rintro _ ⟨y, hy, rfl⟩
  exact key x hx y hy
