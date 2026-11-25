-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:53.396794+00:00
-- url     : https://prove2.me/submissions/bdf328fc-e4d9-4cf9-998b-e4752b5236f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]
namespace PI.MirabolicIndex₂
theorem _root_.solution (n : ℕ) :
    Nat.card {v : Fin (n + 1) → k // v ≠ 0} = Fintype.card k ^ (n + 1) - 1 := by
  classical
  show Nat.card {v : Fin (n + 1) → k // ¬ v = 0} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun,
    Fintype.card_fin]
end PI.MirabolicIndex₂
