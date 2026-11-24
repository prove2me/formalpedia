-- Prove2me | solution 1 for PI.GreenLabelMapW.gen_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:43.586634+00:00
-- url     : https://prove2.me/submissions/235b74d0-23f9-496e-85b2-0cf6465b9922

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
theorem _root_.solution (Cv : LabelConv K) {d : ℕ} (hd : 1 ≤ d) :
    Cv.gen d ^ (Fintype.card K ^ d - 1) = 1 := by
  rw [← Cv.gen_order d hd]
  exact pow_orderOf_eq_one _
end PI.GreenLabelMapW
