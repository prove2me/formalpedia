-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_kSpan_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:37:15.270264+00:00
-- url     : https://prove2.me/submissions/b9824680-c6c7-4181-8ac9-a5f6159bf68c

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  exact fun S hS => hS.2 a b hab y (hy S hS)
end ReciprocityTheory.ChartRestriction.DS.HW
