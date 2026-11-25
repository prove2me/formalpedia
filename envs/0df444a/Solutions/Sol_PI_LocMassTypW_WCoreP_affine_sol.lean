-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.affine_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:13.577296+00:00
-- url     : https://prove2.me/submissions/ac246546-277b-43c9-8cd8-95ec430e11a1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {R : Type*} [CommRing R] {n m : ℕ} (A0 A B0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC' : B0ᵀ * A0 = Bᵀ * A) (X : Matrix (Fin n) (Fin n) R) :
    (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) * A0 = A ∧
      Bᵀ * (k1 A B0 B L0 M + (1 - Mᵀ * Bᵀ) * X * (1 - A0 * L0)) = B0ᵀ := by
  have hBM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have hQ : (1 - A0 * L0) * A0 = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]
  have hP : Bᵀ * (1 - Mᵀ * Bᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBM, Matrix.one_mul, sub_self]
  constructor
  · rw [Matrix.add_mul, Matrix.mul_assoc ((1 - Mᵀ * Bᵀ) * X), hQ, Matrix.mul_zero, add_zero]
    simp only [k1, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hL0, Matrix.mul_one]
    rw [hC']
    abel
  · rw [Matrix.mul_add, ← Matrix.mul_assoc Bᵀ ((1 - Mᵀ * Bᵀ) * X), ← Matrix.mul_assoc Bᵀ, hP,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
    simp only [k1, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hBM, Matrix.one_mul]
    abel
end PI.LocMassTypW.WCoreP
