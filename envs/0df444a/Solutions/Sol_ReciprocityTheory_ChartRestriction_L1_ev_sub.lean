-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ev_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:15.014537+00:00
-- url     : https://prove2.me/submissions/406bb327-26e6-4bef-92f7-66454b44d622

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f - g) x = ev f x - ev g x := by
  have h := (hf.hasSum hx).sub (hg.hasSum hx)
  have e : (fun n => PowerSeries.coeff n (f - g) * x ^ n) =
      fun n => PowerSeries.coeff n f * x ^ n - PowerSeries.coeff n g * x ^ n := by
    funext n
    rw [map_sub, sub_mul]
  rw [← e] at h
  exact h.tsum_eq
end ReciprocityTheory.ChartRestriction.L1
