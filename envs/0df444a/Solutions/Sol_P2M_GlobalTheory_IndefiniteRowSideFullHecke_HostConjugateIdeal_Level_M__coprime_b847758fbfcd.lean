-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_M__coprime_b847758fbfcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:03.104001+00:00
-- url     : https://prove2.me/submissions/a048a125-17e2-440d-85e8-e6240aa9fe6d

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
theorem _root_.solution (L : Level H) {p : ℕ} (hp : p.Prime) : Nat.Coprime p (L.M₀ p) :=
  Nat.coprime_ordCompl hp (by have := L.three_le; omega)
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
