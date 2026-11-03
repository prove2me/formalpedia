-- Prove2me | solution 1 for TurnTables.Reciprocal.proposition_5_part_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:34:08.771101+00:00
-- url     : https://prove2.me/submissions/26adaaa6-9735-4135-a815-c3f11807e235

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

open TurnTables.Reciprocal in
theorem solution (P : Params) (hP : P.Standing)
    (hcase : 2 * P.V1 < P.γ * P.V2) :
    0 < offerProb P ∧ offerProb P < 1 ∧
      IsSymBNE P (strikeB P)
        (fun T => match T with | .part => 1 | .full => offerProb P) := by
  obtain ⟨hγ0, hγ1, hV1, hV2⟩ := hP
  have hV : 0 < P.V2 := by linarith
  have hγV : P.γ * P.V2 < P.V2 := by nlinarith
  have hD : 0 < P.V2 - 2 * P.V1 := by linarith
  have hsum : ∀ f : Impl → ℝ, ∑ E : Impl, f E = f .part + f .full := by
    intro f
    show ∑ E ∈ ({.part, .full} : Finset Impl), f E = _
    rw [Finset.sum_pair (by decide)]
  have c1 : ¬ (P.γ * P.V2 / 2 < P.γ * P.V2 - P.γ * P.V2 / 2) := by
    intro h; linarith
  have c2 : P.γ * P.V2 / 2 < 1 * P.V2 - P.γ * P.V2 / 2 := by linarith
  have hπ0 : 0 < offerProb P := by
    unfold offerProb; exact div_pos (by linarith) hD
  have hπ1 : offerProb P < 1 := by
    unfold offerProb; rw [div_lt_one hD]; linarith
  have hc : offerProb P * (P.V2 - 2 * P.V1) = P.γ * P.V2 - 2 * P.V1 := by
    unfold offerProb; field_simp
  refine ⟨hπ0, hπ1, fun T => by cases T <;> simp <;> constructor <;> linarith, ?_⟩
  intro T a ha0 ha1
  simp only [offerGame, interimPay]
  rw [hsum, hsum]
  generalize offerProb P = π at hc hπ0 hπ1
  cases T <;> simp only [offerorPay, offereePay, Reciprocates, Impl.val, strikeB] <;>
    simp only [c1, c2, if_true, if_false]
  · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hπ1.le))
      (sub_nonneg.2 hcase.le)]
  · have h2 : a * (π * (P.V2 - 2 * P.V1)) = a * (P.γ * P.V2 - 2 * P.V1) := by rw [hc]
    have h3 : π * (π * (P.V2 - 2 * P.V1)) = π * (P.γ * P.V2 - 2 * P.V1) := by rw [hc]
    nlinarith [h2, h3]
