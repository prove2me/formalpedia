-- Prove2me | solution 1 for OblivEllipsoid.Infeas.remark_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:33:16.856816+00:00
-- url     : https://prove2.me/submissions/53686012-6bbc-4a27-a547-a9ceb451276b

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (hA : Assumption11 A) (j : Fin m) (lj : ℝ) (lamj : Fin m → ℝ)
    (hcert : CertLBi A u j lj lamj) (hgap : u j < lj) :
    (¬ ∃ x : Fin n → ℝ, IsFeasible A u x) ∧
      IsAlt A u (lamj + Pi.single j 1) := by
  obtain ⟨h1, h2, h3⟩ := hcert
  have hs : A *ᵥ Pi.single j 1 = OblivEllipsoid.Infeas.col A j := by
    ext k
    simp [OblivEllipsoid.Infeas.col, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hus : u ⬝ᵥ Pi.single j 1 = u j := by
    simp [dotProduct, Pi.single_apply]
  have hcomm : u ⬝ᵥ lamj = lamj ⬝ᵥ u := dotProduct_comm _ _
  have hAmu : A *ᵥ (lamj + Pi.single j 1) = 0 := by
    rw [mulVec_add, h1, hs, neg_add_cancel]
  have hnn : 0 ≤ lamj + Pi.single j 1 := by
    intro k
    have hk : 0 ≤ (Pi.single j (1 : ℝ) : Fin m → ℝ) k := by
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact add_nonneg (h2 k) hk
  have hneg : u ⬝ᵥ (lamj + Pi.single j 1) < 0 := by
    rw [dotProduct_add, hus, hcomm]
    linarith
  refine ⟨?_, ⟨hAmu, hnn, hneg⟩⟩
  rintro ⟨x, hx⟩
  have e : x ⬝ᵥ (A *ᵥ (lamj + Pi.single j 1)) = (Aᵀ *ᵥ x) ⬝ᵥ (lamj + Pi.single j 1) := by
    rw [dotProduct_mulVec, mulVec_transpose]
  rw [hAmu, dotProduct_zero] at e
  have hle : (Aᵀ *ᵥ x) ⬝ᵥ (lamj + Pi.single j 1) ≤ u ⬝ᵥ (lamj + Pi.single j 1) := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hx k) (hnn k)
  linarith
