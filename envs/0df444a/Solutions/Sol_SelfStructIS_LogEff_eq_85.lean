-- Prove2me | solution 1 for SelfStructIS.LogEff.eq_85
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:15:16.433635+00:00
-- url     : https://prove2.me/submissions/66bab0ef-9419-4256-bf23-1912171fc754

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
set_option autoImplicit false
open MeasureTheory Filter Topology SelfStructIS.LogEff

theorem solution (d : ℕ) (ρ u l : ℝ) (hl : 1 < l) (hlu : l ≤ u)
    (y : Fin d → ℝ) (hy : ∀ i, 0 ≤ y i) (x : Fin d → ℝ) (hx : Tmap .two ρ u l x = y) :
    ∀ i, x i ≤ if 1 ≤ y i then y i ^ (Real.log l / Real.log u) else y i := by
  intro i
  have hyi : x i * (u / l) ^ (Real.log (1 + |x i|) / Real.log l) = y i := by
    have := congrFun hx i
    simpa [Tmap, kappa, kappa2] using this
  have hlogl : 0 < Real.log l := Real.log_pos hl
  have hlogu : Real.log l ≤ Real.log u := Real.log_le_log (by linarith) hlu
  have hul : 0 < u / l := div_pos (by linarith) (by linarith)
  have hpos : 0 < (u / l) ^ (Real.log (1 + |x i|) / Real.log l) := Real.rpow_pos_of_pos hul _
  have hxi : 0 ≤ x i := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h hpos
    linarith [hy i]
  set t := x i with ht
  rw [abs_of_nonneg hxi] at hyi
  set a := Real.log u / Real.log l with ha
  have ha1 : 1 ≤ a := by rw [ha, le_div_iff₀ hlogl]; linarith
  have hexp : (u / l) ^ (Real.log (1 + t) / Real.log l) = (1 + t) ^ (a - 1) := by
    rw [Real.rpow_def_of_pos hul, Real.rpow_def_of_pos (by linarith : (0:ℝ) < 1 + t)]
    congr 1
    rw [Real.log_div (by linarith) (by linarith), ha]
    field_simp
  rw [hexp] at hyi
  have h1 : t ^ (a - 1) ≤ (1 + t) ^ (a - 1) :=
    Real.rpow_le_rpow hxi (by linarith) (by linarith)
  have hty : t ≤ y i := by
    rw [← hyi]
    have : 1 ≤ (1 + t) ^ (a - 1) := Real.one_le_rpow (by linarith) (by linarith)
    nlinarith
  have hta : t ^ a ≤ y i := by
    rcases eq_or_lt_of_le hxi with h0 | h0
    · rw [← h0]
      have : (0:ℝ) ^ a = 0 := Real.zero_rpow (by linarith)
      rw [this]; exact hy i
    · have e : t ^ a = t ^ (a - 1) * t := by
        rw [Real.rpow_sub_one h0.ne']; field_simp
      rw [e, ← hyi]
      nlinarith
  split_ifs with h
  · have hy0 := hy i
    have e : Real.log l / Real.log u = a⁻¹ := by rw [ha, inv_div]
    rw [e]
    calc t = (t ^ a) ^ a⁻¹ := (Real.rpow_rpow_inv hxi (by linarith)).symm
      _ ≤ y i ^ a⁻¹ := Real.rpow_le_rpow (Real.rpow_nonneg hxi _) hta (by positivity)
  · exact hty
