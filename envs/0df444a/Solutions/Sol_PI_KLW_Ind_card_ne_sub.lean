-- Prove2me | solution 1 for PI.KLW.Ind.card_ne_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:39.310901+00:00
-- url     : https://prove2.me/submissions/26482fec-80f9-4fb6-96e1-682a0aee3a93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (i0 : ι) (k : ℕ)
    (hk : Fintype.card ι = k + 1) : Fintype.card {i // i ≠ i0} = k := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hk, Nat.add_sub_cancel]
end PI.KLW.Ind
