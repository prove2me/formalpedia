-- Prove2me | solution 1 for PI.SqfDivDeg.W.card_fib_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:59.737677+00:00
-- url     : https://prove2.me/submissions/07ba489b-aecb-43c9-9a2b-0b55b650af63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
import Theorems.Thm_PI_SqfDivDeg_W_card_Mon
import Theorems.Thm_PI_SqfDivDeg_W_mem_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (n : ℕ) (c : ZMod g) :
    g ^ n ≤ ((Mon g (n + 1)).filter (fun f => f.IsRoot c)).card := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun h => (X - C c) * h)
  · intro h hh
    have hh' : h ∈ Mon g n := by simpa using hh
    rw [mem_Mon] at hh'
    have : (X - C c) * h ∈ (Mon g (n + 1)).filter (fun f => f.IsRoot c) := by
      rw [Finset.mem_filter, mem_Mon]
      refine ⟨⟨(monic_X_sub_C c).mul hh'.1, ?_⟩, ?_⟩
      · rw [(monic_X_sub_C c).natDegree_mul hh'.1, natDegree_X_sub_C, hh'.2]
        ring
      · simp [IsRoot]
    simpa using this
  · intro h1 _ h2 _ e
    exact mul_left_cancel₀ (X_sub_C_ne_zero c) e
end PI.SqfDivDeg.W
