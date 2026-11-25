-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.phiRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:18:03.358258+00:00
-- url     : https://prove2.me/submissions/2bc7d00e-e880-42db-9cf8-5ebb5068b62b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F}
variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (s t : Fam D F k) : PhiRel D F k p w s t ↔ PhiVal p w s.s t.s := by
  constructor
  · rintro H α _ rfl T ρ z J hJ
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw α
    rw [← hv u hu hc T ρ z J hJ]
    exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu hc) _ ρ.left z J hJ
  · intro H α u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have := H α _ rfl _ (𝟙 _) y J hJ
    rw [← (gen_phi hG p w hw α).2 u hu hc _ (𝟙 _) y J hJ] at this
    exact this
end ReciprocityTheory.ChartRestriction.G.DVR
