-- Prove2me | solution 1 for PI.SqfRootShift.W.lte_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:33.051846+00:00
-- url     : https://prove2.me/submissions/d24a1b8d-f007-4d7c-9a60-0b5a71904369

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {p g k : ℕ} [Fact p.Prime] (hp : Odd p) (hg : 2 ≤ g) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k := by
  have hx : ¬ p ∣ g := by
    intro h
    have h1 : p ∣ g - 1 + 1 := by rwa [show g - 1 + 1 = g by omega]
    have h2 : p ∣ 1 := (Nat.dvd_add_right hpg).mp h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  have := padicValNat.pow_sub_pow (p := p) (x := g) (y := 1) hp (by omega) (by simpa using hpg)
    hx hk
  simpa using this
end PI.SqfRootShift.W
