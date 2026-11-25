-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_rhoSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:45.383682+00:00
-- url     : https://prove2.me/submissions/0e6eaac8-0598-4d7e-8ca7-893f5afbfb7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_cont_Lsq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  have h1 := cont_Lsq (p := p) (m := m) (Fin.last p)
  have h2 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h3 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  exact (h1.add h2).add h3
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
