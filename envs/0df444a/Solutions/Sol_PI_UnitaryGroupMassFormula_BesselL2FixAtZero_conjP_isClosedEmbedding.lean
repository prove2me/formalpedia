-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_isClosedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:37:41.635613+00:00
-- url     : https://prove2.me/submissions/a3ccebad-2bfd-43f0-8510-3cad6d1d02f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero
variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)
namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero
theorem _root_.solution (hP : IsUnit P) : IsClosedEmbedding (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₜ (Fin n → Fin n → ℂ) :=
    { toFun := fun m => Matrix.of.symm (P⁻¹ * m * P)
      invFun := fun x => P * Matrix.of x * P⁻¹
      left_inv := fun m => by
        show P * (P⁻¹ * m * P) * P⁻¹ = m
        calc P * (P⁻¹ * m * P) * P⁻¹ = (P * P⁻¹) * m * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = m := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun x => by
        show P⁻¹ * (P * Matrix.of x * P⁻¹) * P = Matrix.of x
        calc P⁻¹ * (P * Matrix.of x * P⁻¹) * P = (P⁻¹ * P) * Matrix.of x * (P⁻¹ * P) := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.of x := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := by
        show Continuous fun m : Matrix (Fin n) (Fin n) ℂ => P⁻¹ * m * P
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := by
        show Continuous fun x : Fin n → Fin n → ℂ => P * Matrix.of x * P⁻¹
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact e.isClosedEmbedding.comp (isClosedEmbeddingMatrix n ε).1
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
