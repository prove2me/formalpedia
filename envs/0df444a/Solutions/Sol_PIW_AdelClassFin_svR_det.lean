-- Prove2me | solution 1 for PIW.AdelClassFin.svR_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:51.815169+00:00
-- url     : https://prove2.me/submissions/4ee7b1d6-f2c1-458f-946c-dfb77e779e10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace PIW.AdelClassFin
theorem _root_.solution (eq : κ ≃ ι) (X : Matrix ι κ ℂ) (B : Matrix ι ι ℂ) :
    (Xᴴ * B * X).det = star (X.submatrix eq id).det * B.det * (X.submatrix eq id).det := by
  have hY : Xᴴ * B * X = (X.submatrix eq id)ᴴ * B.submatrix eq eq * X.submatrix eq id := by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  rw [hY, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_submatrix_equiv_self]
end PIW.AdelClassFin
