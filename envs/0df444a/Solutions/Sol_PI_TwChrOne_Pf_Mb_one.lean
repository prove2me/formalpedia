-- Prove2me | solution 1 for PI.TwChrOne.Pf.Mb_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:44.989659+00:00
-- url     : https://prove2.me/submissions/3fb58e1f-9eb4-4efe-8556-bf5b8190b97c

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
import Theorems.Thm_PI_TwChrOne_Pf_reduction_zero
import Theorems.Thm_PI_TwChrOne_Pf_atN_dI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}
namespace PI.TwChrOne.Pf
theorem _root_.solution : Mb P kj N c (1 : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) = 1 := by
  ext s t
  simp only [Mb, Ment, Matrix.map_apply, Matrix.of_apply, atN_dI]
  by_cases hst : s = t
  · subst hst
    simp [Loc.eN, dI, reduction_one₂]
  · have hv : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
    rw [Matrix.one_apply_ne hst]
    simp [Loc.eN, dI, hv, reduction_zero]
end PI.TwChrOne.Pf
