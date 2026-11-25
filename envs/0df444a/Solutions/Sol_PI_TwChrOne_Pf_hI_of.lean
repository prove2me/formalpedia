-- Prove2me | solution 1 for PI.TwChrOne.Pf.hI_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:27.433459+00:00
-- url     : https://prove2.me/submissions/a38273d0-9ace-4f73-83d3-cc0d5d741b03

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_ent_int

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
theorem _root_.solution {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i) :=
  fun j i => ent_int P (Subgroup.mem_inf.1 hr).1 j i
end PI.TwChrOne.Pf
