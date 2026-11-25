-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__card_uni_1d6088473d01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:55.740823+00:00
-- url     : https://prove2.me/submissions/206aebf6-784f-407f-891a-aa88a0246189

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
import Theorems.Thm_P2M_PI_MirabolicIndex__card_pairs_b8f39c05cf6e

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
    Nat.card {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Fintype.card k ^ ((n + 1) * n / 2) := by
  classical
  rw [Nat.card_congr (uniEquiv (k := k) n), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]
end PI.MirabolicIndex₂
