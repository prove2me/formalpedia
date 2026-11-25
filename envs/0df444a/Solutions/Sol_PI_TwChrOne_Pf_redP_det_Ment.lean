-- Prove2me | solution 1 for PI.TwChrOne.Pf.redP_det_Ment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:48.625486+00:00
-- url     : https://prove2.me/submissions/2d25f6f9-50a0-47d1-9808-f99e490c80db

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_reduction_det
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
theorem _root_.solution {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i)) :
    redP P (Ment kj N c r).det = (Mb P kj N c r).det :=
  reduction_det P _ fun s t => by
    show IntAt P (Loc.atN _ (kj + s.1))
    rw [atN_dI]
    exact hrI _ _
end PI.TwChrOne.Pf
