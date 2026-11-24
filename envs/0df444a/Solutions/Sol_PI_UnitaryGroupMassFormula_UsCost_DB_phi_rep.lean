-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DB.phi_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:10:06.2038+00:00
-- url     : https://prove2.me/submissions/d3c3cdb7-ef4c-429b-8ca3-5e5a38c6fa6b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB

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
theorem _root_.solution (hSZ : SliceZ) (ξ : Xi k p s ρ σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) (Z' : G.Mat s) :
    gaXi k ρ σ d ξ Z' γ = gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
      muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z') * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
      Rn k (p + s) ρ ξ.1.2) := by
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have := hSZ k p s ρ σ d ξ Z ((Matrix.of Z)⁻¹ * Matrix.of Z') γ
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mul] at this
  exact this
end PI.UnitaryGroupMassFormula.UsCost.DB
