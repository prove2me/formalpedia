-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Host_w__add_conj_0cbd56f4b1a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:56.424876+00:00
-- url     : https://prove2.me/submissions/a0aeee1c-6c41-4a7a-8629-37c8f09c94d8

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
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
variable (H : Host E)
namespace GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
theorem _root_.solution : H.w₀ + conjO E H.w₀ = 1 := by
  apply RingOfIntegers.ext
  change (1 + H.s) / 2 + IsCMField.complexConj E ((1 + H.s) / 2) = 1
  rw [map_div₀, map_add, map_one, H.isCMField_complexConj_s_eq_neg, map_ofNat]
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
