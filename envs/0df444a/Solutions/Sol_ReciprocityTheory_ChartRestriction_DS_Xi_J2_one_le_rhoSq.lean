-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.one_le_rhoSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:46.507023+00:00
-- url     : https://prove2.me/submissions/81575397-6c79-45af-b9cb-3eba86412574

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_one_le_lsq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := one_le_lsq x (Fin.last p)
  have : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  linarith
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
