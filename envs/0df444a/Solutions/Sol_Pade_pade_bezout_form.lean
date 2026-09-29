-- Prove2me | solution 1 for Pade.pade_bezout_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:51:07.038719+00:00
-- url     : https://prove2.me/submissions/6134f07a-447e-4b7b-aa1d-4801505bf039

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

open Pade

theorem solution {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) :
    (∀ k ≤ m + n, PowerSeries.coeff k ((Q : PowerSeries F) * f - (P : PowerSeries F)) = 0) ↔
      ∃ K : Polynomial F,
        P = Q * PowerSeries.trunc (m + n + 1) f + K * X ^ (m + n + 1) := by
  set N := m + n + 1
  have htr : (PowerSeries.X : PowerSeries F) ^ N ∣ f - (PowerSeries.trunc N f : PowerSeries F) := by
    refine PowerSeries.X_pow_dvd_iff.2 (fun j hj => ?_)
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hj, sub_self]
  constructor
  · intro h
    have h1 : (PowerSeries.X : PowerSeries F) ^ N ∣ (Q : PowerSeries F) * f - P :=
      PowerSeries.X_pow_dvd_iff.2 (fun j hj => h j (by omega))
    have h2 : (X : Polynomial F) ^ N ∣ P - Q * PowerSeries.trunc N f := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have h3 : (PowerSeries.X : PowerSeries F) ^ N ∣
          ((P - Q * PowerSeries.trunc N f : Polynomial F) : PowerSeries F) := by
        have : ((P - Q * PowerSeries.trunc N f : Polynomial F) : PowerSeries F) =
            (Q : PowerSeries F) * (f - (PowerSeries.trunc N f : PowerSeries F))
              - ((Q : PowerSeries F) * f - P) := by push_cast; ring
        rw [this]; exact dvd_sub (dvd_mul_of_dvd_right htr _) h1
      rw [← Polynomial.coeff_coe]
      exact PowerSeries.X_pow_dvd_iff.1 h3 d hd
    obtain ⟨K, hK⟩ := h2
    exact ⟨K, by rw [mul_comm K, ← hK]; ring⟩
  · rintro ⟨K, hK⟩ k hk
    have : (Q : PowerSeries F) * f - (P : PowerSeries F) =
        (Q : PowerSeries F) * (f - (PowerSeries.trunc N f : PowerSeries F))
          - (K : PowerSeries F) * PowerSeries.X ^ N := by
      rw [hK]; push_cast; ring
    have h4 : (PowerSeries.X : PowerSeries F) ^ N ∣ (Q : PowerSeries F) * f - (P : PowerSeries F) := by
      rw [this]; exact dvd_sub (dvd_mul_of_dvd_right htr _) (dvd_mul_left _ _)
    exact PowerSeries.X_pow_dvd_iff.1 h4 k (by omega)
