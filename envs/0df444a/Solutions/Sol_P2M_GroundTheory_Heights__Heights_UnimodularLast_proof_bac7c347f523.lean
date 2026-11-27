-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_UnimodularLast_proof_bac7c347f523
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:38.918339+00:00
-- url     : https://prove2.me/submissions/958f5a7a-8499-443a-b388-6aa9f6ea11c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PUnimodularLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_UnimodularLast_exists_basis_d879db4ccda8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace UnimodularLast
theorem _root_.solution : UnimodularLast.Statement := by
  intro k ρ hρ
  obtain ⟨b, hker, hlast⟩ := UnimodularLast.exists_basis k ρ hρ
  refine ⟨(Pi.basisFun ℤ (Fin (k + 1))).toMatrix b, ?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  · intro j
    have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.castSucc j) =
        ρ ⬝ᵥ b (Fin.castSucc j) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hker j
  · have : (ρ ᵥ* (Pi.basisFun ℤ (Fin (k + 1))).toMatrix b) (Fin.last k) =
        ρ ⬝ᵥ b (Fin.last k) := by
      simp only [vecMul, dotProduct, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this]
    exact hlast
end UnimodularLast
end GroundTheory.Heights₂.Heights
