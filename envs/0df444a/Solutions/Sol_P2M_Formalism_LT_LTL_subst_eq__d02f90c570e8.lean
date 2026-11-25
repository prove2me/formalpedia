-- Prove2me | solution 1 for P2M_Formalism_LT_LTL_subst_eq__d02f90c570e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:01.547806+00:00
-- url     : https://prove2.me/submissions/2adab144-0a58-4576-93bd-11b0a888db84

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_P2M_Formalism_LT_LTL_decomp__fc31821dd2a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution (f : PowerSeries K) (h0 : constantCoeff f = 0) {a : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = coeff 1 f • a + a ^ 2 * (tail2 f).subst a := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp' f h0]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_smul ha, PowerSeries.subst_mul ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
end Formalism.LT.LTL
