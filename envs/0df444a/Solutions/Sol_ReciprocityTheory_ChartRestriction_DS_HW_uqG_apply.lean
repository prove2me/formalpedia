-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uqG_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:50.485135+00:00
-- url     : https://prove2.me/submissions/aba3af13-410e-433f-abcf-174a1fc552ca

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n)
    (x : WithLp 2 (V × V')) :
    WithLp.ofLp (uqG F F' a b x) = (F a b (WithLp.ofLp x).1, F' a b (WithLp.ofLp x).2) := rfl
end ReciprocityTheory.ChartRestriction.DS.HW
