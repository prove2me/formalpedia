-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.fbOf_canon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:39.67715+00:00
-- url     : https://prove2.me/submissions/e9f0f61f-9844-4c1b-be92-ba7d877e12c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_FK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_actK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_biext_change_first_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_biext_change_second_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_toKs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_toKad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
variable {R k O : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing O] [StarRing O] {d : ℕ}
variable {B : FB k d O} (t : IntTie (algebraMap R k) B) (hφ : Function.Injective (algebraMap R k))
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
theorem _root_.solution (h : PS k 2 d) (hB : B.IsCanonGauge k h) : (fbOf t hφ).IsCanonGauge k h := by
  refine ⟨hB.ax0, hB.ax1, ?_, ?_, ?_, ?_⟩
  · rw [biext_change_first_factor, fbOf_FK]; exact hB.ph1
  · rw [biext_change_second_factor, fbOf_FK]; exact hB.ph2
  · rw [fbOf_toKs]; exact hB.sy
  · intro a; rw [fbOf_toKad, fbOf_actK, fbOf_actK]; exact hB.ad a
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
