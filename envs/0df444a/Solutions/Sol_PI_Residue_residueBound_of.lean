-- Prove2me | solution 1 for PI.Residue.residueBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:18.756403+00:00
-- url     : https://prove2.me/submissions/3c638e00-7a22-4ef3-ade9-98f53718dec0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Residue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_ResidueBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (hA1 : ZetaLePow) (hA2 : ZetaRLe) (hB : HeckeLower) (hC : Optimise) :
    PI.ResidueBound := by
  obtain ⟨C, hC1, hC⟩ := hC
  refine ⟨C, hC1, fun E _ _ hm => ?_⟩
  have hd : 4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ E ≤ ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.abs_discr_ge (K := E) (by omega)
    exact_mod_cast this
  obtain ⟨s, hs, hle⟩ := hC (Module.finrank ℚ E) _ hm hd
  obtain ⟨hsum, hz⟩ := hA1 E s hs
  refine (hB E s hs hsum).trans (le_trans ?_ hle)
  have hd0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hz0 : 0 ≤ zetaR s := tsum_nonneg fun n => by positivity
  gcongr
  exact hz.trans (pow_le_pow_left₀ hz0 (hA2 s hs) _)
end PI.Residue
