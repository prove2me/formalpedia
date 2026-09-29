-- Prove2me | solution 1 for Pade.pade_normalization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:50:54.89099+00:00
-- url     : https://prove2.me/submissions/02f86f46-b1af-4139-8efe-8c96a614cf67

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) (h : IsPadeApproximant f m n P Q) (hQ : Q.coeff 0 ≠ 0) :
    IsPadeApproximant f m n (C (Q.coeff 0)⁻¹ * P) (C (Q.coeff 0)⁻¹ * Q) ∧
      (C (Q.coeff 0)⁻¹ * Q).coeff 0 = 1 := by
  obtain ⟨h0, hP, hQd, hc⟩ := h
  have hu : (Q.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hQ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact mul_ne_zero (by simpa using hu) h0
  · rw [degree_C_mul hu]; exact hP
  · rw [degree_C_mul hu]; exact hQd
  · intro k hk
    have : ((C (Q.coeff 0)⁻¹ * Q : Polynomial F) : PowerSeries F) * f
        - ((C (Q.coeff 0)⁻¹ * P : Polynomial F) : PowerSeries F)
        = PowerSeries.C (Q.coeff 0)⁻¹ * ((Q : PowerSeries F) * f - (P : PowerSeries F)) := by
      push_cast; ring
    rw [this, PowerSeries.coeff_C_mul, hc k hk, mul_zero]
  · rw [coeff_C_mul]; exact inv_mul_cancel₀ hQ
