-- Prove2me | solution 1 for P2M_PI_OneCosetSharp_W_Nums_n__ge_f7fc7b2f5918
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:07.825124+00:00
-- url     : https://prove2.me/submissions/5903791d-c5f9-4efc-8924-b807eee75c7b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
namespace PI.OneCosetSharp.W
namespace Nums
theorem _root_.solution {k₀ m t j n' c n : ℕ} (hn : Nums k₀ m t j n' c n) : k₀ ≤ n' := by
  obtain ⟨-, -, h4, hj1, hj2, hc, h7, -⟩ := hn
  generalize (j - 1) * t = X at h7
  omega
end Nums
end PI.OneCosetSharp.W
