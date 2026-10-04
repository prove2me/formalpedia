-- Prove2me | solution 1 for TheoryOfGames.Utility.segment_mono_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:03:49.884252+00:00
-- url     : https://prove2.me/submissions/dd5339d8-0841-425e-b64f-7b3f8601f5e3

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

set_option autoImplicit false

namespace TheoryOfGames.Utility

theorem ce0b_cmb_lt_cmb {U : Type*} (S : UtilitySystem U) {u v : U} (huv : S.lt u v)
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

theorem ce0b_gt_irrefl {U : Type*} (S : UtilitySystem U) (x : U) : ¬ S.gt x x := by
  rcases S.complete x x with h | h | h
  · exact h.2.1
  · exact fun _ => h.2.1 rfl
  · exact fun _ => h.2.1 rfl

theorem ce0b_bounds {U : Type*} (S : UtilitySystem U) {u v : U} (huv : S.lt u v)
    (α : OpenUnit) : S.lt u (S.cmb α u v) ∧ S.lt (S.cmb α u v) v := by
  refine ⟨S.lt_mix_of_lt _ u v huv, ?_⟩
  unfold UtilitySystem.lt UtilitySystem.cmb
  rw [S.mix_comm]
  exact S.mix_lt_of_gt _ v u huv

end TheoryOfGames.Utility

open TheoryOfGames.Utility in
theorem solution {U : Type*} (S : UtilitySystem U) {u₀ v₀ : U}
    (h : S.lt u₀ v₀) :
    (∀ α : OpenUnit, S.lt u₀ (S.cmb α u₀ v₀) ∧ S.lt (S.cmb α u₀ v₀) v₀) ∧
      Function.Injective (fun α : OpenUnit => S.cmb α u₀ v₀) ∧
      ∀ α β : OpenUnit, (α : ℝ) < (β : ℝ) → S.lt (S.cmb α u₀ v₀) (S.cmb β u₀ v₀) := by
  refine ⟨fun α => ce0b_bounds S h α, ?_, fun α β hab => ce0b_cmb_lt_cmb S h hab⟩
  intro α β hab
  simp only at hab
  by_contra hne
  have hne' : (α : ℝ) ≠ (β : ℝ) := fun e => hne (Subtype.ext e)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have := ce0b_cmb_lt_cmb S h hlt
    unfold UtilitySystem.lt at this
    rw [hab] at this
    exact ce0b_gt_irrefl S _ this
  · have := ce0b_cmb_lt_cmb S h hlt
    unfold UtilitySystem.lt at this
    rw [hab] at this
    exact ce0b_gt_irrefl S _ this
