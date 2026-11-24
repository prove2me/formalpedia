-- Prove2me | solution 1 for PI.GreenLabelMapW.card_pow_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:00.020573+00:00
-- url     : https://prove2.me/submissions/7df6f6f5-d909-42d2-a3c6-149f2c6717ea

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
theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Fintype.card K ^ d - 1 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h2 : 2 ≤ Fintype.card K ^ d := le_trans hq (Nat.le_self_pow (by omega) _)
  omega
end PI.GreenLabelMapW
