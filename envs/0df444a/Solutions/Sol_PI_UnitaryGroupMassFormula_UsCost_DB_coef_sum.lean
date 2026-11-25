-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DB.coef_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:37.831481+00:00
-- url     : https://prove2.me/submissions/87807775-688b-4e60-83a7-e9a339e833ef

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
namespace PI.UnitaryGroupMassFormula.UsCost.DB
theorem _root_.solution {s : ℕ} (Z W : G.Mat s) :
    ∑ i : Fin s × Fin s × Bool, coefZ Z W i • eMat i.1 i.2.1 i.2.2 = (Matrix.of Z)⁻¹ * Matrix.of W := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, eMat, Matrix.of_apply]
  simp [Fintype.sum_prod_type, smul_ite, ite_and, Finset.sum_ite_eq, coefZ,
    Complex.real_smul, Complex.re_add_im]
end PI.UnitaryGroupMassFormula.UsCost.DB
