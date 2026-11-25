-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__mirabIndex_f365ed63d8b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:45.908132+00:00
-- url     : https://prove2.me/submissions/ece88d23-6b3c-49fc-83e8-42239c7be4c8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
import Theorems.Thm_P2M_PI_MirabolicIndex__card_mirab_5807049d95f2
import Theorems.Thm_P2M_PI_MirabolicIndex__card_uni_1d6088473d01

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
theorem _root_.solution : MirabIndex := by
  unfold PI.MirabIndex.MirabIndex
  intro k _ _ n
  rw [card_mirab, card_uni]
end PI.MirabolicIndex₂
