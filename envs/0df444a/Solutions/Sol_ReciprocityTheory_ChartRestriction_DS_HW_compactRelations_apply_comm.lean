-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.compactRelations_apply_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:50.742408+00:00
-- url     : https://prove2.me/submissions/be08e767-3ef7-4ab5-99eb-12901ff5d92a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_CompactRelationsApplyComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {a b c d : Fin n}
    (h1 : ε a = ε b) (h2 : ε c = ε d) (x : M) :
    F a b (F c d x) = F c d (F a b x) + (if b = c then F a d x else 0) -
      (if d = a then F c b x else 0) := by
  have h := congrArg (fun T : Module.End ℂ M => T x) (hF a b c d h1 h2)
  simp only [LinearMap.sub_apply] at h
  have h2' : F a b (F c d x) - F c d (F a b x) =
      (if b = c then F a d else 0) x - (if d = a then F c b else 0) x := h
  have h' := eq_add_of_sub_eq h2'
  rw [h']
  split_ifs <;> (try simp only [LinearMap.zero_apply]) <;> abel
end ReciprocityTheory.ChartRestriction.DS.HW
