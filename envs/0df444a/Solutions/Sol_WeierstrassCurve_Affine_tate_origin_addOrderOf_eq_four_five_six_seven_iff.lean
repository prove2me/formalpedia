-- Prove2me | solution 1 for WeierstrassCurve.Affine.tate_origin_addOrderOf_eq_four_five_six_seven_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:12:08.46295+00:00
-- url     : https://prove2.me/submissions/d716f69f-2e19-4874-82b4-d59484a31061

import Mathlib
import Definitions.Def_RPLib_S2_TateNFB

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (b c : F) (hb : b ≠ 0)
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve F).toAffine.Nonsingular 0 0) :
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 4 ↔ c = 0) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 5 ↔ b = c) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 6 ↔ b = c + c ^ 2) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 7 ↔ b ^ 2 - b * c - c ^ 3 = 0) := by
  have key : ∀ M : ℕ, 0 < M →
      (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = M ↔ RPLib.TateNF.HasExactOrder M b c) := by
    intro M hM
    rw [RPLib.TateNF.hasExactOrder_iff hM, RPLib.TateNF.tatePt_of_ne hb]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key 4 (by norm_num), RPLib.TateNF.hasExactOrder_four_iff]
    exact ⟨fun h4 => h4.2, fun h4 => ⟨hb, h4⟩⟩
  · rw [key 5 (by norm_num), RPLib.TateNF.hasExactOrder_five_iff]
    exact ⟨fun h5 => h5.2, fun h5 => ⟨hb, h5⟩⟩
  · rw [key 6 (by norm_num), RPLib.TateNF.hasExactOrder_six_iff]
    refine ⟨fun h6 => h6.2.2, fun h6 => ⟨hb, ?_, h6⟩⟩
    rintro rfl
    exact hb (by simpa using h6)
  · rw [key 7 (by norm_num), RPLib.TateNF.hasExactOrder_seven_iff]
    refine ⟨fun h7 => h7.2.2, fun h7 => ⟨hb, ?_, h7⟩⟩
    rintro rfl
    exact hb (by simpa using h7)

