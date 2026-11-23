-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:03.71286+00:00
-- url     : https://prove2.me/submissions/fc902d69-e873-4ce2-b8d8-5ce9b0f30771

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
theorem _root_.solution {a b : K} {I J : FractionalIdeal (𝓞 K)⁰ K}
    (ha : IsLocGen p a I) (hb : IsLocGen p b J) (hI : I ≠ 0) (hJ : J ≠ 0) : IsLocGen p (a * b) (I * J) := by
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨hb0, hbc⟩ := hb
  refine ⟨mul_ne_zero ha0 hb0, ?_⟩
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr ha0
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hb0
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul (K := K) (v := p) hsa hsb,
    FractionalIdeal.count_mul (K := K) (v := p) hI hJ, hac, hbc]
end IsLocGen
end Formalism.L2.LamCM
