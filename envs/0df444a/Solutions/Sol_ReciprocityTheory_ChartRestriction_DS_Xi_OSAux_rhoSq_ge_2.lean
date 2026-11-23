-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:53.387155+00:00
-- url     : https://prove2.me/submissions/e4cfb720-c7f0-4ac5-a5a5-70221dba2c87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_mono

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  have h1 := Lsq_mono x (Fin.le_last l')
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  linarith
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
