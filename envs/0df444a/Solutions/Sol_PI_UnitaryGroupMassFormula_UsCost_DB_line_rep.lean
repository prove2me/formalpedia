-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DB.line_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:38.782061+00:00
-- url     : https://prove2.me/submissions/af4038f2-2f90-4cfb-946b-0a6d6c6f6a97

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_block_matrix_two_line
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_phi_rep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_U_inv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost.DB
theorem _root_.solution (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (W : G.Mat s)
    (t : ℝ) :
    gaXi k ρ σ d ξ (Z + t • W) γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ (1 + t • ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1)) *
      Rn k (p + s) ρ ξ.1.2) := by
  rw [phi_rep hSZ ξ hZ γ (Z + t • W)]
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have e1 : (Matrix.of Z)⁻¹ * Matrix.of (Z + t • W) = 1 + t • ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have : Matrix.of (Z + t • W) = Matrix.of Z + t • Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.nonsing_inv_mul _ hZu, Matrix.mul_smul]
  rw [e1, block_matrix_two_line, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, U_inv_mul, Matrix.mul_smul, Matrix.smul_mul]
end PI.UnitaryGroupMassFormula.UsCost.DB
