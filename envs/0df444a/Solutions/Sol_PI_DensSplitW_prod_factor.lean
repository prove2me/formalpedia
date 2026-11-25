-- Prove2me | solution 1 for PI.DensSplitW.prod_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:11.969784+00:00
-- url     : https://prove2.me/submissions/d85f8c68-ca5d-48c7-8339-9c39b49fbcb9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange
import Theorems.Thm_PI_DensSplitW_sub_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution (q b c : ℕ) (hq : 0 < q) (hc : c ≤ b) :
    ((∏ i ∈ range c, (q ^ b - q ^ i) : ℕ) : ℝ) =
      (q : ℝ) ^ (b * c) * ∏ i ∈ range c, (1 - ((q : ℝ) ^ (b - i))⁻¹) := by
  rw [Nat.cast_prod]
  rw [Finset.prod_congr rfl (fun i hi => sub_factor q b i hq
    (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hc)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
end PI.DensSplitW
