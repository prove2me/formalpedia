-- Prove2me | solution 1 for RoboAdvising.Interaction.Rtilde_deriv_one_neg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:00:20.12231+00:00
-- url     : https://prove2.me/submissions/9c90d9f6-ebda-4a84-98b3-d71583707536

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

set_option autoImplicit false
open RoboAdvising.Interaction

lemma ra_fd (P : Params) (hS : P.Standing) (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (fAux P)
      (-(P.β*P.sig0) / (2 * Real.sqrt φ * φ) * (1 - (φ-1)/2*P.pe)
        - P.β*P.sig0*P.pe/(2*Real.sqrt φ)
        - (P.β*P.sig0)^2 * Real.sqrt φ / (2*φ^2*Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ)) * ((φ-1)/2*P.pe)
        + Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / Real.sqrt φ * (P.pe/2)) φ := by
  obtain ⟨h0, hse, -⟩ := hS
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hH : 0 < P.β^2*P.sig0^2/φ + P.se^2 := by positivity
  have h1 : HasDerivAt Real.sqrt (1/(2*Real.sqrt φ)) φ := Real.hasDerivAt_sqrt hφ.ne'
  have hA := (hasDerivAt_const φ (P.β*P.sig0)).div h1 hu.ne'
  have hT0 : HasDerivAt (fun x : ℝ => (x-1)/2) (1/2) φ :=
    ((hasDerivAt_id φ).sub_const 1).div_const 2
  have hL : HasDerivAt (fun x : ℝ => 1 - (x-1)/2*P.pe) (-(1/2*P.pe)) φ := by
    simpa using (hT0.mul_const P.pe).const_sub 1
  have hq := (hasDerivAt_const φ (P.β^2*P.sig0^2)).div (hasDerivAt_id φ) hφ.ne'
  have hB := (hq.add_const (P.se^2)).sqrt hH.ne'
  have hf := (hA.mul hL).add ((hB.mul hT0).mul_const P.pe)
  have hw : Real.sqrt (P.β^2*P.sig0^2/φ + P.se^2) = Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / Real.sqrt φ := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  refine HasDerivAt.congr_deriv hf ?_
  simp only [id, Pi.div_apply]
  rw [hw]
  have hwpos : 0 < Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  have e2 : P.β^2*P.sig0^2 = (P.β*P.sig0)^2 := by ring
  rw [e2]
  clear hf hA hB hq hL hT0 h1 hw hH
  generalize Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) = w at *
  generalize P.β*P.sig0 = a at *
  generalize Real.sqrt φ = u at *
  subst hsq
  field_simp
  ring

lemma ra_q (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (φ : ℝ) (hφ : 0 ≤ φ) :
    Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) =
      Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) / (P.β*P.sig0) := by
  obtain ⟨h0, hse, -⟩ := hS
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have : 1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2) = ((P.β*P.sig0)^2 + P.se^2*φ) / (P.β*P.sig0)^2 := by
    field_simp
  rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq ha.le]

lemma ra_hasDerivAt_f (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (fAux P) (1 / 2 * (P.β * P.sig0 * P.pe / φ ^ 2) * gAux P φ) φ := by
  have h := ra_fd P hS φ hφ
  have hS' := hS
  obtain ⟨h0, hse, -⟩ := hS
  refine HasDerivAt.congr_deriv h ?_
  have hq := ra_q P hS' hβ φ hφ.le
  unfold gAux
  rw [hq]
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have hwpos : 0 < Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) := Real.sqrt_pos.2 (by positivity)
  have hu : 0 < Real.sqrt φ := Real.sqrt_pos.2 hφ
  have hsq : Real.sqrt φ ^ 2 = φ := Real.sq_sqrt hφ.le
  clear h hq hS'
  generalize Real.sqrt ((P.β*P.sig0)^2 + P.se^2*φ) = w at *
  generalize P.β*P.sig0 = a at *
  generalize Real.sqrt φ = u at *
  generalize P.pe = p at *
  subst hsq
  field_simp
  ring

theorem solution (P : Params) (hS : P.Standing) (hβ : 0 < P.β)
    (h : P.pe * P.se / (P.β * P.sig0) < 1) :
    ∃ d : ℝ, HasDerivAt (Rtilde P) d 1 ∧ d < 0 := by
  have hS' := hS
  obtain ⟨h0, hse, hp0, hp1, -⟩ := hS
  have ha : 0 < P.β * P.sig0 := mul_pos hβ h0
  have hps : P.pe * P.se < P.β * P.sig0 := by
    rwa [div_lt_one ha] at h
  have hf := ra_fd P hS' 1 one_pos
  have hf' : HasDerivAt (fAux P) ((-(P.β * P.sig0) - P.β * P.sig0 * P.pe
      + P.pe * Real.sqrt ((P.β * P.sig0) ^ 2 + P.se ^ 2)) / 2) 1 := by
    refine HasDerivAt.congr_deriv hf ?_
    simp only [Real.sqrt_one, one_pow, mul_one, sub_self, zero_div, zero_mul, sub_zero]
    ring
  have hR : Rtilde P = fun φ => Real.sqrt (2 / Real.pi) * fAux P φ := rfl
  refine ⟨Real.sqrt (2 / Real.pi) * ((-(P.β * P.sig0) - P.β * P.sig0 * P.pe
      + P.pe * Real.sqrt ((P.β * P.sig0) ^ 2 + P.se ^ 2)) / 2), ?_, ?_⟩
  · rw [hR]; exact hf'.const_mul _
  · have hc : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
    refine mul_neg_of_pos_of_neg hc ?_
    have hw : Real.sqrt ((P.β * P.sig0) ^ 2 + P.se ^ 2) ≤ P.β * P.sig0 + P.se := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have hw2 : P.pe * Real.sqrt ((P.β * P.sig0) ^ 2 + P.se ^ 2) ≤ P.pe * (P.β * P.sig0 + P.se) :=
      mul_le_mul_of_nonneg_left hw hp0
    nlinarith
