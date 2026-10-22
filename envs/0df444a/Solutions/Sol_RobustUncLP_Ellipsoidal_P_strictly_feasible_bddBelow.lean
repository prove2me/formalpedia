-- Prove2me | solution 1 for RobustUncLP.Ellipsoidal.P_strictly_feasible_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:10:29.493822+00:00
-- url     : https://prove2.me/submissions/a5319165-16fd-4d77-b63d-6671cdbfe3f3

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC



namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

theorem psf_core {m n k : ℕ} (D : EllipsoidalData m n k)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    (∃ u ∈ PFeas D, ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) < 1) ∧
      ∀ (x : Fin n → ℝ) (i : Fin m),
        BddBelow ((fun u => (D.Pi 0 (u 0) *ᵥ x) i) '' PFeas D) := by
  constructor
  · obtain ⟨A, hA⟩ := hC
    choose u hu1 hu2 using hA
    refine ⟨u, ⟨fun ℓ => ?_, fun ℓ => (hu2 ℓ).le⟩, hu2⟩
    rw [← hu1 ℓ, ← hu1 0]
  · intro x i
    obtain ⟨C, hC⟩ := hB
    refine ⟨-(C * ∑ j, |x j|), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hmem : D.Pi 0 (u 0) ∈ D.uncSet := by
      refine Set.mem_iInter.2 fun ℓ => ?_
      exact ⟨u ℓ, (hu.1 ℓ).symm, hu.2 ℓ⟩
    have h1 : |(D.Pi 0 (u 0) *ᵥ x) i| ≤ C * ∑ j, |x j| := by
      simp only [mulVec, dotProduct]
      calc |∑ j, D.Pi 0 (u 0) i j * x j| ≤ ∑ j, |D.Pi 0 (u 0) i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, C * |x j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hC _ hmem i j) (abs_nonneg _)
        _ = C * ∑ j, |x j| := by rw [Finset.mul_sum]
    linarith [neg_abs_le ((D.Pi 0 (u 0) *ᵥ x) i)]

end RobustUncLP.Ellipsoidal

open RobustUncLP.Ellipsoidal
open Matrix EllipsoidalData

theorem solution {m n k : ℕ} (D : EllipsoidalData m n k)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    (∃ u ∈ PFeas D, ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) < 1) ∧
      ∀ (x : Fin n → ℝ) (i : Fin m),
        BddBelow ((fun u => (D.Pi 0 (u 0) *ᵥ x) i) '' PFeas D) := by
  exact psf_core D hB hC
