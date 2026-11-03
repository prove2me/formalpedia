-- Prove2me | solution 1 for TurnTables.Reciprocal.proposition_5_part_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:34:08.004356+00:00
-- url     : https://prove2.me/submissions/749c9395-5264-49e1-be6d-03fa85d73cb1

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

open TurnTables.Reciprocal in
theorem solution (P : Params) (hP : P.Standing)
    (hcase : P.γ * P.V2 ≤ 2 * P.V1) :
    IsSymBNE P (strikeB P)
      (fun T => match T with | .part => 0 | .full => 1) := by
  obtain ⟨hγ0, hγ1, hV1, hV2⟩ := hP
  have hV : 0 < P.V2 := by linarith
  have hγV : P.γ * P.V2 < P.V2 := by nlinarith
  have hsum : ∀ f : Impl → ℝ, ∑ E : Impl, f E = f .part + f .full := by
    intro f
    show ∑ E ∈ ({.part, .full} : Finset Impl), f E = _
    rw [Finset.sum_pair (by decide)]
  have c1 : ¬ (P.γ * P.V2 / 2 < P.γ * P.V2 - P.γ * P.V2 / 2) := by
    intro h; linarith
  have c2 : P.γ * P.V2 / 2 < 1 * P.V2 - P.γ * P.V2 / 2 := by linarith
  refine ⟨fun T => by cases T <;> norm_num, ?_⟩
  intro T a ha0 ha1
  simp only [offerGame, interimPay]
  rw [hsum, hsum]
  cases T <;> simp only [offerorPay, offereePay, Reciprocates, Impl.val, strikeB] <;>
    simp only [c1, c2, if_true, if_false]
  · nlinarith [mul_nonneg ha0 (sub_nonneg.2 hcase)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hV2.le)]
