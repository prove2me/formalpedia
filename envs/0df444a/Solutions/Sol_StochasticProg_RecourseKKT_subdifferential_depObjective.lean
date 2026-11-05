-- Prove2me | solution 1 for StochasticProg.RecourseKKT.subdifferential_depObjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T00:52:04.557573+00:00
-- url     : https://prove2.me/submissions/33898332-98ee-47e3-b966-7c2168123394

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_depObjective
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential

set_option autoImplicit false

namespace P2MSubdiffDep

lemma aux_le (a x : ℝ) (e : EReal) :
    ((x : ℝ) : EReal) ≤ (a : EReal) + e ↔ ((x - a : ℝ) : EReal) ≤ e := by
  induction e using EReal.rec with
  | bot =>
    exact iff_of_false (by rw [EReal.add_bot, le_bot_iff]; exact EReal.coe_ne_bot _)
      (by rw [le_bot_iff]; exact EReal.coe_ne_bot _)
  | top => exact iff_of_true (by rw [EReal.coe_add_top]; exact le_top) le_top
  | coe s =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma aux_eq (a r : ℝ) (e : EReal) :
    (a : EReal) + e = (r : EReal) ↔ e = ((r - a : ℝ) : EReal) := by
  induction e using EReal.rec with
  | bot => exact iff_of_false (by rw [EReal.add_bot]; exact EReal.bot_ne_coe _) (EReal.bot_ne_coe _)
  | top =>
    exact iff_of_false (by rw [EReal.coe_add_top]; exact EReal.top_ne_coe _) (EReal.top_ne_coe _)
  | coe s =>
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff, EReal.coe_eq_coe_iff]
    constructor <;> intro h <;> linarith

end P2MSubdiffDep

open MeasureTheory Matrix StochasticProg.RecourseKKT in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2) (xs : Fin n1 → ℝ) :
    subdifferential (depObjective P pb) xs =
      (fun ζ => pb.c + ζ) '' subdifferential (expectedRecourse P pb) xs := by
  ext η
  constructor
  · rintro ⟨r, hr, h⟩
    unfold depObjective at hr h
    rw [P2MSubdiffDep.aux_eq] at hr
    refine ⟨η - pb.c, ⟨r - pb.c ⬝ᵥ xs, hr, fun w => ?_⟩, by simp⟩
    have hw := h w
    rw [P2MSubdiffDep.aux_le] at hw
    have e : r - pb.c ⬝ᵥ xs + (η - pb.c) ⬝ᵥ (w - xs) = r + η ⬝ᵥ (w - xs) - pb.c ⬝ᵥ w := by
      simp only [sub_dotProduct, dotProduct_sub]; ring
    rw [e]; exact hw
  · rintro ⟨ζ, ⟨r, hr, h⟩, rfl⟩
    refine ⟨pb.c ⬝ᵥ xs + r, ?_, fun w => ?_⟩
    · unfold depObjective; rw [hr, EReal.coe_add]
    · unfold depObjective
      rw [P2MSubdiffDep.aux_le]
      have e : pb.c ⬝ᵥ xs + r + (pb.c + ζ) ⬝ᵥ (w - xs) - pb.c ⬝ᵥ w = r + ζ ⬝ᵥ (w - xs) := by
        simp only [add_dotProduct, dotProduct_sub]; ring
      rw [e]; exact h w
