-- Prove2me | solution 1 for TheoryOfGames.Utility.cmb_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:57:16.43874+00:00
-- url     : https://prove2.me/submissions/7ca5a424-8e1a-400f-b914-5cb534dbd57f

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

set_option autoImplicit false

namespace P430bd26a

open TheoryOfGames.Utility

theorem irrefl {U : Type*} (S : UtilitySystem U) (x : U) : ¬ S.gt x x := by
  intro h
  rcases S.complete x x with ⟨_, h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩
  · exact h1 h
  · exact h2 rfl
  · exact h2 rfl

theorem mix_self {U : Type*} (S : UtilitySystem U) (α : OpenUnit) (u : U) :
    S.mix α u u = u := by
  obtain ⟨ha0, ha1⟩ := α.2
  set a : ℝ := (α : ℝ) with ha
  -- p = α/2, q = 1 - p, r = p/q
  have hp0 : (0 : ℝ) < a / 2 := by linarith
  have hp1 : a / 2 < 1 := by linarith
  let half : OpenUnit := ⟨1 / 2, by norm_num, by norm_num⟩
  let p : OpenUnit := ⟨a / 2, hp0, hp1⟩
  let q : OpenUnit := OpenUnit.oneSub p
  have hq : (q : ℝ) = 1 - a / 2 := rfl
  have hq0 : (0 : ℝ) < 1 - a / 2 := by linarith
  have hr0 : (0 : ℝ) < (a / 2) / (1 - a / 2) := div_pos hp0 hq0
  have hr1 : (a / 2) / (1 - a / 2) < 1 := by
    rw [div_lt_one hq0]; linarith
  let r : OpenUnit := ⟨(a / 2) / (1 - a / 2), hr0, hr1⟩
  have hhalf : OpenUnit.mul half α = p := by
    apply Subtype.ext
    show (1 / 2 : ℝ) * a = a / 2
    ring
  have hrq : OpenUnit.mul r q = p := by
    apply Subtype.ext
    show (a / 2) / (1 - a / 2) * (1 - a / 2) = a / 2
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hq0.ne', mul_one]
  set w := S.mix α u u with hw
  have hfp : S.mix p u u = S.mix half w u := by
    rw [hw, S.mix_mix, hhalf]
  have hfq : S.mix q u u = S.mix p u u := (S.mix_comm p u u).symm
  have hfpr : S.mix p u u = S.mix r (S.mix q u u) u := by
    rw [S.mix_mix, hrq]
  rcases S.complete w u with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
  · exact h
  · exfalso
    -- w > u
    have h1 : S.gt (S.mix p u u) u := by
      rw [hfp, S.mix_comm]
      exact S.lt_mix_of_lt _ u w h
    have h2 : S.gt (S.mix q u u) u := by rw [hfq]; exact h1
    have h3 := S.mix_lt_of_gt r _ u h2
    rw [← hfpr, ← hfq] at h3
    exact irrefl S _ h3
  · exfalso
    -- u > w
    have h1 : S.gt u (S.mix p u u) := by
      rw [hfp, S.mix_comm]
      exact S.mix_lt_of_gt _ u w h
    have h2 : S.gt u (S.mix q u u) := by rw [hfq]; exact h1
    have h3 := S.lt_mix_of_lt r _ u h2
    rw [← hfpr, ← hfq] at h3
    exact irrefl S _ h3

end P430bd26a

open TheoryOfGames.Utility in
theorem solution {U : Type*} (S : UtilitySystem U) (γ : OpenUnit) (u : U) :
    S.cmb γ u u = u := by
  exact P430bd26a.mix_self S _ u
