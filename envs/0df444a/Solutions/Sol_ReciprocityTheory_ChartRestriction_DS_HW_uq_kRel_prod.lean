-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_kRel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:19:08.204687+00:00
-- url     : https://prove2.me/submissions/185609d7-84e6-4023-a893-31d2aa469736

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
theorem _root_.solution {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A)
    (F' : Fin n → Fin n → B) (h : KRel ε F) (h' : KRel ε F') : KRel ε (fun a b => (F a b, F' a b)) := by
  intro a b c d hab hcd
  refine Prod.ext ?_ ?_
  · first
      | (simp only [Prod.fst_sub, Prod.fst_mul, h a b c d hab hcd, apply_ite Prod.fst, Prod.fst_zero]; done)
      | simp [h a b c d hab hcd, apply_ite Prod.fst]
  · first
      | (simp only [Prod.snd_sub, Prod.snd_mul, h' a b c d hab hcd, apply_ite Prod.snd, Prod.snd_zero]; done)
      | simp [h' a b c d hab hcd, apply_ite Prod.snd]
end ReciprocityTheory.ChartRestriction.DS.HW
