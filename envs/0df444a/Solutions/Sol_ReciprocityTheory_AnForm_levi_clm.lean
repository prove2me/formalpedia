-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:30.679647+00:00
-- url     : https://prove2.me/submissions/6eb510a2-cb62-4fe8-8a55-32c20670773d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution (L : (ι → ℂ) →L[ℝ] ℝ) (z w : ι → ℂ) : levi (⇑L) z w = 0 := by
  have h : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
  simp [levi, h]
end ReciprocityTheory.AnForm
