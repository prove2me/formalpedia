-- Prove2me | solution 1 for OnDemandCoord.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:08:14.74214+00:00
-- url     : https://prove2.me/submissions/33b499f9-e1af-4b29-aea2-3ff9e01b2b01

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

open MeasureTheory ProbabilityTheory

open OnDemandCoord in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (K : Contract n) (hβ : ∀ i, 0 < K.β i) (i : Fin n) (Q : Fin n → ℝ) (hQ : 0 ≤ Q) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (hκ : IsPolicy κ) :
    M.firmCost K i Q κ η = M.p * (1 - K.m i) * M.mean Q i + M.c * Q i + K.r i := by
  haveI := M.isProb
  haveI := hκ.1
  have hS : 0 ≤ M.S η := by
    unfold Model.S
    apply mul_nonneg M.N_pos.le
    by_cases h : η ≤ M.τl
    · rw [M.G_of_le η h]
    · have h1 := M.monotone_G (le_of_not_ge h)
      rw [M.G_of_le M.τl le_rfl] at h1
      exact h1
  have hx0 : ∀ ω, 0 ≤ M.vacVec Q ω := fun ω j => le_max_right _ _
  have hinner : ∀ ω, ∫ a, (M.p * max (M.vac Q i ω - a i) 0 + M.payment K i a (M.vacVec Q ω))
      ∂κ (M.vacVec Q ω, M.S η) = M.p * (1 - K.m i) * M.vac Q i ω + K.r i := by
    intro ω
    have hae := hκ.2 (M.vacVec Q ω) (M.S η) (hx0 ω) hS
    rw [integral_congr_ae (g := fun _ => M.p * (1 - K.m i) * M.vac Q i ω + K.r i) ?_]
    · simp
    · filter_upwards [hae] with a ha
      have h1 := ha.1 i
      have hvi : M.vacVec Q ω i = M.vac Q i ω := rfl
      rw [hvi] at h1
      simp only [Model.payment, Model.fixedRate, Model.contingentPayment, hvi]
      rw [max_eq_left (by linarith [h1.2])]
      have := (hβ i).ne'
      field_simp
      ring
  have hvint : Integrable (fun ω => M.vac Q i ω) P :=
    ((M.integrable_X i).sub (integrable_const (Q i))).pos_part
  unfold Model.firmCost Model.mean
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_add (hvint.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring
