-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.rationalParameters_tensor_independent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:58:36.129223+00:00
-- url     : https://prove2.me/submissions/45e144f1-66cd-4331-be7a-4548e7339015

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section RationalParameters

variable {R C A M : Type u} [CommRing R]

variable [AddCommGroup C] [Module R C] [Coalgebra R C]

variable [Ring A] [Algebra R A]

variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]


/-- Remark 2.10, PDF p.6: rational parameters depend only on their tensor. -/
theorem solution [IsScalarTower R A M] (b : C →ₗ[R] A →ₗ[R] R)
    (h : IsRationalPairing b) (m : M) {n k : ℕ}
    (ms : Fin n → M) (cs : Fin n → C) (ns : Fin k → M) (ds : Fin k → C)
    (hm : IsRationalParameters b m ms cs)
    (heq : (∑ i, ms i ⊗ₜ[R] cs i) = ∑ j, ns j ⊗ₜ[R] ds j) :
    IsRationalParameters b m ns ds := by
  intro a
  have key : ∀ {k : ℕ} (ns : Fin k → M) (ds : Fin k → C),
      (∑ j, b (ds j) a • ns j) = pairingAlpha b M (∑ j, ns j ⊗ₜ[R] ds j) a := by
    intro k ns ds
    rw [map_sum, LinearMap.sum_apply]
    rfl
  rw [hm a, key, key, heq]


end RationalParameters



end
