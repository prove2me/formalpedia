-- Prove2me | solution 1 for StrategicObfuscation.posterior_le_prior
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:43:29.566696+00:00
-- url     : https://prove2.me/submissions/88c1bab7-579f-4b0f-92dd-a86571a68c01

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium

open Set

open StrategicObfuscation in
theorem solution {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Ico (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    Q ≤ p ∧
    (c < Q * V ↔ (1 - p) * c * (1 - π σ e) < p * (V - c) * (1 - π σ 0)) := by
  have hσ' : σ ∈ Icc (0:ℝ) 1 := ⟨hσ.1, hσ.2.le⟩
  have hA : π σ 0 < 1 := by
    have := hπ.strictMono_zero σ hσ' 1 ⟨zero_le_one, le_rfl⟩ hσ.2
    rwa [hπ.one_zero] at this
  have he0 : 0 ≤ e := by
    rw [heq.effort]; exact (hE α heq.mem_alpha σ hσ').1
  have hB : π σ e ≤ π σ 0 := hπ.anti_effort σ hσ' 0 e le_rfl he0
  have bayes := heq.bayes
  set A := 1 - π σ 0 with hAdef
  set B := 1 - π σ e with hBdef
  have hApos : 0 < A := by linarith
  have hBA : A ≤ B := by linarith
  set D := A * p + B * (1 - p) with hD
  have hDpos : 0 < D := by nlinarith
  have hQD : Q * D = A * p := by rw [hD]; linarith [bayes]
  constructor
  · have h1 : Q * D ≤ p * D := by
      rw [hQD, hD]
      nlinarith [mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (sub_nonneg.mpr hBA)]
    exact le_of_mul_le_mul_right h1 hDpos
  · have key : c < Q * V ↔ c * D < Q * D * V := by
      rw [show Q * D * V = Q * V * D by ring]
      exact ⟨fun h => mul_lt_mul_of_pos_right h hDpos, fun h => lt_of_mul_lt_mul_right h hDpos.le⟩
    rw [key, hQD, hD]
    constructor <;> intro h <;> nlinarith
