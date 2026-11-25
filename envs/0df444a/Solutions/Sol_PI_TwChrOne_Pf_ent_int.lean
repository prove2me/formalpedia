-- Prove2me | solution 1 for PI.TwChrOne.Pf.ent_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:20.021939+00:00
-- url     : https://prove2.me/submissions/4ba5c4e4-73ca-49e0-8061-9d7783c95a3d

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Theorems.Thm_PI_TwChrOne_Pf_int_of_mem_stdAt
import Theorems.Thm_PI_TwChrOne_Pf_eN_mem

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
namespace PI.TwChrOne.Pf
theorem _root_.solution {r : Sp E n ≃ₗ[E] Sp E n} (hr : r ∈ stabL E n (stdAt E n P)) (j : ℕ) (i : Fin n) :
    IntAt P (r (Loc.eN E n j) i) :=
  int_of_mem_stdAt P ((hr _).2 (eN_mem P j)) i
end PI.TwChrOne.Pf
