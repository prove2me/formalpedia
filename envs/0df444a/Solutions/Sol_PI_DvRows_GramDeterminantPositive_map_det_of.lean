-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.map_det_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:03.583274+00:00
-- url     : https://prove2.me/submissions/372b9858-3c02-406f-b619-092282835b73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (φ : K →+* ℂ) {d : ℕ} (F : Fin d → Fin d → K) :
    φ (Matrix.of F).det = (Matrix.of fun i j => φ (F i j)).det := by
  rw [RingHom.map_det]; rfl
end PI.DvRows.GramDeterminantPositive
