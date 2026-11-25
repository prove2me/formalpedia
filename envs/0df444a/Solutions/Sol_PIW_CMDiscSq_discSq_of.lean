-- Prove2me | solution 1 for PIW.CMDiscSq.discSq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:29:05.716906+00:00
-- url     : https://prove2.me/submissions/25f50501-05e3-4a1f-9393-394fa651b67e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution (h1 : RelDiffTop) (h2 : RelDegTwo) : Formalism.L2.SG.MassRatio.DiscSq := by
  intro F E _ _ _ _ _ _ hFE
  have hN := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) E (𝓞 E)
  rw [h1 F E hFE, Ideal.absNorm_top, one_mul, h2 F E hFE] at hN
  have hR : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hN
  unfold Formalism.L2.SG.MassRatio.dF
  simpa [Nat.cast_natAbs, Int.cast_abs] using hR
end PIW.CMDiscSq
