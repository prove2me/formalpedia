-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isoRel_inj_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:36.633894+00:00
-- url     : https://prove2.me/submissions/897ae55c-fca4-4b7f-acdd-90b55982efb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gs_isoRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Y : Scheme.{0}} {L M : LB Y}
namespace ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
theorem _root_.solution (hL : L.IsLB) {w : LB.Iso L M} {s : LB.Sec L} {s' t' : LB.Sec M} (hs : IsoRel w s s')
    (ht : IsoRel w s t') : s' = t' := by
  have hf : s'.f = t'.f := by
    funext i
    refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL y
    rw [gs_isoRel hs i k y hy hk, gs_isoRel ht i k y hy hk]
  cases s'; cases t'; simp only at hf; subst hf; rfl
end ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
