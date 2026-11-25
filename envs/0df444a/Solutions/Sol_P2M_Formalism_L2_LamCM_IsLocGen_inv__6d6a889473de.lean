-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_IsLocGen_inv__6d6a889473de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:37.109023+00:00
-- url     : https://prove2.me/submissions/77481774-0533-445e-b66c-eb2b952dd200

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
theorem _root_.solution {a : K} {I : FractionalIdeal (𝓞 K)⁰ K} (ha : IsLocGen p a I) : IsLocGen p a⁻¹ I⁻¹ := by
  obtain ⟨ha0, hac⟩ := ha
  refine ⟨inv_ne_zero ha0, ?_⟩
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, FractionalIdeal.count_inv, hac]
end IsLocGen
end Formalism.L2.LamCM
