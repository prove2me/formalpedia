-- Prove2me | solution 1 for TheoryOfGames.Utility.cmb_lt_cmb_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:15:43.099959+00:00
-- url     : https://prove2.me/submissions/f1d40495-6963-4cdb-8064-46581bd28b23

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

set_option autoImplicit false

namespace TheoryOfGames.Utility

/-- (A:A): if `u < v`, then `α < β` implies `(1 − α)u + αv < (1 − β)u + βv`. -/
theorem cmb_lt_cmb_of_lt_aux {U : Type*} (S : UtilitySystem U) {u v : U} (huv : S.lt u v)
    {α β : OpenUnit} (hαβ : (α : ℝ) < (β : ℝ)) :
    S.lt (S.cmb α u v) (S.cmb β u v) := by
  obtain ⟨ha0, ha1⟩ := α.2
  obtain ⟨hb0, hb1⟩ := β.2
  have h1a : (0 : ℝ) < 1 - (α : ℝ) := by linarith
  let a : OpenUnit := ⟨(1 - (β : ℝ)) / (1 - (α : ℝ)), by
    refine ⟨div_pos (by linarith) h1a, ?_⟩
    rw [div_lt_one h1a]; linarith⟩
  set w := S.cmb α u v with hw
  have hvw : S.gt v w := by
    have hcomm : w = S.mix α v u := by
      rw [hw, UtilitySystem.cmb, S.mix_comm]
      congr 1
      apply Subtype.ext
      simp [OpenUnit.oneSub]
    rw [hcomm]
    exact S.mix_lt_of_gt α v u huv
  have hβ : S.cmb β u v = S.mix a w v := by
    rw [hw, UtilitySystem.cmb, UtilitySystem.cmb, S.mix_mix]
    congr 1
    apply Subtype.ext
    simp only [OpenUnit.mul, OpenUnit.oneSub, a]
    field_simp
  unfold UtilitySystem.lt
  rw [hβ]
  exact S.lt_mix_of_lt a w v hvw

end TheoryOfGames.Utility

open TheoryOfGames.Utility in
theorem solution {U : Type*} (S : UtilitySystem U) {u v : U} (huv : S.lt u v)
    {α β : OpenUnit} (hαβ : (α : ℝ) < (β : ℝ)) :
    S.lt (S.cmb α u v) (S.cmb β u v) := by
  exact cmb_lt_cmb_of_lt_aux S huv hαβ

