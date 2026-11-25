-- Prove2me | solution 1 for PI.CntNotIntW.val_one_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:06.067215+00:00
-- url     : https://prove2.me/submissions/14d3f76b-fbb6-49e6-b1d3-e45f0b046d9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_ValOneOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open NumberField IsDedekindDomain ValuativeRel
variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [ValuativeRel K]
namespace PI.CntNotIntW
theorem _root_.solution (σ : E →+* K) (l : ℕ) (hl0 : l ≠ 0) (hl : valuation K (l : K) < 1) (s : 𝓞 E)
    (hs : s ∉ (vPrime σ l hl0 hl).asIdeal) : valuation K (σ (s : E)) = 1 :=
  le_antisymm (sig_le_one σ s) (not_lt.1 hs)
end PI.CntNotIntW
