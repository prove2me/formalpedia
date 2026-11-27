-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__pos_9f8643595328
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:06.508705+00:00
-- url     : https://prove2.me/submissions/eb2e67d2-676b-4246-b8bf-f849d82ccf2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
variable {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
theorem _root_.solution (L : Level H) : 0 < L.M' :=
  Nat.lcm_pos (by have := L.three_le; omega) L.one_le
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
