-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_IsLocGen_pow__280537c55445
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:19.100212+00:00
-- url     : https://prove2.me/submissions/01e9a0a6-b052-4fe4-b0e6-e61010b181d0

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
namespace Formalism.L2.LamCM
namespace IsLocGen
theorem _root_.solution {a : K} {I : FractionalIdeal (𝓞 K)⁰ K} (ha : IsLocGen p a I) (k : ℕ) :
    IsLocGen p (a ^ k) (I ^ k) := by
  obtain ⟨ha0, hac⟩ := ha
  refine ⟨pow_ne_zero _ ha0, ?_⟩
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, FractionalIdeal.count_pow, hac]
end IsLocGen
end Formalism.L2.LamCM
