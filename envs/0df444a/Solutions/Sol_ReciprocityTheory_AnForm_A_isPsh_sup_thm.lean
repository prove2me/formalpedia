-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.isPsh_sup_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:55.886849+00:00
-- url     : https://prove2.me/submissions/cfd01bc7-7f17-40b5-b0a5-6923d30f8729

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_PshInh_ii_sup__a1047692b6a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Set Filter Topology Real PshInh
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : IsPsh_supStatement := by
  intro D ι _ _ U u hU hu
  refine ⟨?_, fun z w hdisc => ?_⟩
  · intro x hx y hy
    have : ∀ j, ∀ᶠ x' in 𝓝[U] x, u j x' < y := fun j =>
      (hu j).1 x hx y (lt_of_le_of_lt (Finset.le_sup' (fun j => u j x) (Finset.mem_univ j)) hy)
    filter_upwards [Filter.eventually_all.2 this] with x' hx'
    exact (Finset.sup'_lt_iff _).2 fun j _ => hx' j
  · have hci : ∀ j, CircleIntegrable (fun ζ : ℂ => u j (z + ζ • w)) 0 1 :=
      fun j => ((hu j).2 z w hdisc).1
    have hcs : CircleIntegrable (fun ζ : ℂ =>
        Finset.univ.sup' Finset.univ_nonempty (fun j => u j (z + ζ • w))) 0 1 :=
      ii_sup' (fun j θ => u j (z + circleMap 0 1 θ • w)) hci
    refine ⟨hcs, ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => u j z)
    simp only
    rw [hj]
    refine ((hu j).2 z w hdisc).2.trans (Real.circleAverage_mono (hci j) hcs fun ζ _ => ?_)
    exact Finset.le_sup' (fun j => u j (z + ζ • w)) (Finset.mem_univ j)
end ReciprocityTheory.AnForm.A
