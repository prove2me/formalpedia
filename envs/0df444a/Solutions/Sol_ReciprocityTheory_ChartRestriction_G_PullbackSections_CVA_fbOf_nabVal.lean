-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.fbOf_nabVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:45.073119+00:00
-- url     : https://prove2.me/submissions/f73753ac-df98-456e-89c4-ea9cc2930843

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_FK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_fbOf_actK

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
theorem _root_.solution (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (fbOf t hφ).nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by
  unfold FB.nabVal FB.hL
  rw [fbOf_FK, fbOf_actK]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
