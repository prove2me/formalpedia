-- Prove2me | solution 1 for SPOBounds.StronglyConvex.strength_property
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:00:27.347335+00:00
-- url     : https://prove2.me/submissions/4aad86a2-25a4-4fdc-b5f4-8b4db688b7e1

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

theorem aux_scsp_nu_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hSnt : S.Nontrivial) (c : StrongDual ℝ E) :
    SPOBounds.Shared.nu S c ≤ ‖c‖ := by
  obtain ⟨u, hu, v, hv, huv⟩ := hSnt
  have h0 : (0 : StrongDual ℝ E) ∈ SPOBounds.Shared.degenerate S := by
    refine ⟨u, hu, v, hv, huv, ?_, ?_⟩
    · intro x _; simp
    · intro x _; simp
  have := Metric.infDist_le_dist_of_mem (x := c) h0
  simpa [SPOBounds.Shared.nu, dist_zero_right] using this

theorem aux_scsp_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S)
    (c : StrongDual ℝ E) (w0 : E) (hw0 : w0 ∈ S) (hmin : ∀ v ∈ S, c w0 ≤ c v)
    (v : E) (hv : v ∈ S) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) * (μbar / 2 * ‖c‖ * ‖v - w0‖ ^ 2) ≤ c (v - w0) := by
  set r := (μbar / 2) * t * (1 - t) * ‖v - w0‖ ^ 2 with hr
  have hball := hSsc.2 v hv w0 hw0 t ⟨ht0.le, ht1.le⟩
  set m := t • v + (1 - t) • w0 with hm
  have hcm : c m = t * c v + (1 - t) * c w0 := by simp [hm]
  have hC : 0 ≤ t * c (v - w0) := by
    have := hmin v hv
    rw [map_sub]
    have : 0 ≤ c v - c w0 := by linarith
    positivity
  have h1t : 0 < 1 - t := by linarith
  have key : r * ‖c‖ ≤ t * c (v - w0) := by
    rcases (show 0 ≤ r by positivity).eq_or_lt with h | h
    · rw [← h]; simpa using hC
    · have hle : ‖c‖ ≤ t * c (v - w0) / r := by
        refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC h.le) (fun x hx => ?_)
        have hy : ‖r • x‖ = r := by rw [norm_smul, hx, Real.norm_eq_abs, abs_of_pos h, mul_one]
        have h1 : m + r • x ∈ S := hball (by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hy])
        have h2 : m - r • x ∈ S := hball (by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, hy])
        have e1 := hmin _ h1
        have e2 := hmin _ h2
        rw [map_add, hcm, map_smul, smul_eq_mul] at e1
        rw [map_sub, hcm, map_smul, smul_eq_mul] at e2
        rw [le_div_iff₀ h, Real.norm_eq_abs, map_sub]
        rcases abs_cases (c x) with ⟨hx', _⟩ | ⟨hx', _⟩ <;> rw [hx'] <;> nlinarith
      rw [le_div_iff₀ h] at hle
      linarith
  have : t * ((1 - t) * (μbar / 2 * ‖c‖ * ‖v - w0‖ ^ 2)) ≤ t * c (v - w0) := by
    have : r * ‖c‖ = t * ((1 - t) * (μbar / 2 * ‖c‖ * ‖v - w0‖ ^ 2)) := by rw [hr]; ring
    linarith
  exact le_of_mul_le_mul_left this ht0

theorem aux_scsp_lim {X Y : ℝ} (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * X ≤ Y)
    (hY : 0 ≤ Y) : X ≤ Y := by
  by_contra hXY
  rw [not_le] at hXY
  have hX : 0 < X := lt_of_le_of_lt hY hXY
  have ht0 : 0 < (X - Y) / (2 * X) := div_pos (sub_pos.2 hXY) (by linarith)
  have ht1 : (X - Y) / (2 * X) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have := h _ ht0 ht1
  have e : (1 - (X - Y) / (2 * X)) * X = (X + Y) / 2 := by field_simp; ring
  rw [e] at this
  linarith

end SPOBounds.StronglyConvex

open SPOBounds.StronglyConvex

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ v ∈ S, c (w c) ≤ c v) :
    SPOBounds.Shared.StrengthProperty S μbar w := by
  intro c v hv
  obtain ⟨hwS, hmin⟩ := hw c
  have hY : 0 ≤ c (v - w c) := by rw [map_sub]; linarith [hmin v hv]
  have hlim : μbar / 2 * ‖c‖ * ‖v - w c‖ ^ 2 ≤ c (v - w c) :=
    aux_scsp_lim (fun t ht0 ht1 => aux_scsp_step hμ hSsc c (w c) hwS hmin v hv t ht0 ht1) hY
  have hnu := aux_scsp_nu_le hSnt c
  calc μbar * SPOBounds.Shared.nu S c / 2 * ‖v - w c‖ ^ 2
      ≤ μbar / 2 * ‖c‖ * ‖v - w c‖ ^ 2 := by
        have h1 : 0 ≤ ‖v - w c‖ ^ 2 := by positivity
        have h2 : μbar * SPOBounds.Shared.nu S c ≤ μbar * ‖c‖ :=
          mul_le_mul_of_nonneg_left hnu hμ.le
        nlinarith
    _ ≤ c (v - w c) := hlim
