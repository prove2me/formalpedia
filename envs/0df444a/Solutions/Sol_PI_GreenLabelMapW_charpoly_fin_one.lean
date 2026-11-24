-- Prove2me | solution 1 for PI.GreenLabelMapW.charpoly_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:43.973224+00:00
-- url     : https://prove2.me/submissions/5cfdb545-d2b2-4bba-a16b-7875d9f4eeac

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (A : Matrix (Fin 1) (Fin 1) K) :
    A.charpoly = X - Polynomial.C (A 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Fin.default_eq_zero, Matrix.charmatrix_apply_eq]
end PI.GreenLabelMapW
