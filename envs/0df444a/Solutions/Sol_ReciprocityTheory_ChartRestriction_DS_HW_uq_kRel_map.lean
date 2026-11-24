-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_kRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:11.413188+00:00
-- url     : https://prove2.me/submissions/9536b579-8f34-4b0a-a0ba-2ee3f036d90a

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
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A) (f : A →+* B)
    (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have h0 := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul, apply_ite f, map_zero] at h0
  exact h0
end ReciprocityTheory.ChartRestriction.DS.HW
