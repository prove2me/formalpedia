-- Prove2me | solution 1 for PetruzziDada.Additive.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:54:51.580156+00:00
-- url     : https://prove2.me/submissions/e818a78f-1a05-4fb3-8bcd-143e2b8bfb50

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory
open PetruzziDada.Additive

namespace G69PD
variable (M : Model)

lemma f_eq_ind : M.f = (Set.Icc M.A M.B).indicator M.f := by
  funext u; by_cases hu : u ∈ Set.Icc M.A M.B
  · simp [hu]
  · simp [hu, M.f_eq_zero u hu]

lemma intOn : IntegrableOn M.f (Set.Icc M.A M.B) := by
  have h := M.f_integrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le M.A_lt_B.le] at h
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr h

lemma intf : Integrable M.f := by
  rw [f_eq_ind M]; exact (integrable_indicator_iff measurableSet_Icc).mpr (intOn M)

lemma intuf : Integrable (fun u => u * M.f u) := by
  have : (fun u => u * M.f u) = (Set.Icc M.A M.B).indicator (fun u => u * M.f u) := by
    funext u; by_cases hu : u ∈ Set.Icc M.A M.B
    · simp [hu]
    · simp [hu, M.f_eq_zero u hu]
  rw [this]
  refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
  exact (intOn M).continuousOn_mul continuousOn_id isCompact_Icc

lemma ii (a b : ℝ) : IntervalIntegrable M.f volume a b := (intf M).intervalIntegrable
lemma iiu (a b : ℝ) : IntervalIntegrable (fun u => u * M.f u) volume a b := (intuf M).intervalIntegrable

lemma Fsplit (z : ℝ) : (∫ u in z..M.B, M.f u) = 1 - M.F z := by
  have := intervalIntegral.integral_add_adjacent_intervals (ii M M.A z) (ii M z M.B)
  rw [M.f_total] at this; unfold Model.F; linarith

lemma musplit (z : ℝ) : (∫ u in z..M.B, u * M.f u) = M.μ - ∫ u in M.A..z, u * M.f u := by
  have := intervalIntegral.integral_add_adjacent_intervals (iiu M M.A z) (iiu M z M.B)
  unfold Model.μ; linarith

lemma Λ_eq (z : ℝ) : M.Λ z = z * M.F z - ∫ u in M.A..z, u * M.f u := by
  unfold Model.Λ Model.F
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub ((ii M _ _).const_mul z) (iiu M _ _), intervalIntegral.integral_const_mul]

lemma Θ_eq (z : ℝ) : M.Θ z = (M.μ - ∫ u in M.A..z, u * M.f u) - z * (1 - M.F z) := by
  unfold Model.Θ
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (iiu M _ _) ((ii M _ _).const_mul z), intervalIntegral.integral_const_mul,
    musplit, Fsplit]

lemma eq1 (z p : ℝ) : M.expProfit z p = M.Ψ p - M.L z p := by
  have e1 : (∫ u in M.A..z, (p * (M.y p + u) - M.h * (z - u)) * M.f u)
      = (p * M.y p - M.h * z) * M.F z + (p + M.h) * ∫ u in M.A..z, u * M.f u := by
    have : (fun u => (p * (M.y p + u) - M.h * (z - u)) * M.f u)
        = fun u => (p * M.y p - M.h * z) * M.f u + (p + M.h) * (u * M.f u) := by funext u; ring
    rw [this, intervalIntegral.integral_add ((ii M _ _).const_mul _) ((iiu M _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; rfl
  have e2 : (∫ u in z..M.B, (p * (M.y p + z) - M.s * (u - z)) * M.f u)
      = (p * (M.y p + z) + M.s * z) * (1 - M.F z) - M.s * (M.μ - ∫ u in M.A..z, u * M.f u) := by
    have : (fun u => (p * (M.y p + z) - M.s * (u - z)) * M.f u)
        = fun u => (p * (M.y p + z) + M.s * z) * M.f u - M.s * (u * M.f u) := by funext u; ring
    rw [this, intervalIntegral.integral_sub ((ii M _ _).const_mul _) ((iiu M _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, Fsplit, musplit]
  unfold Model.expProfit Model.Ψ Model.L
  rw [e1, e2, Λ_eq, Θ_eq]
  ring

end G69PD


open MeasureTheory
open PetruzziDada.Additive
/-- Eqs. (1)–(3), p. 184: the expected-profit integral equals the riskless profit less the
expected loss, `E[Π(z, p)] = Ψ(p) - L(z, p)`, for every stocking factor `z` and price `p`. -/
theorem solution (M : Model) (z p : ℝ) : M.expProfit z p = M.Ψ p - M.L z p := by
  exact G69PD.eq1 M z p

