-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp__de63461cc6c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:46.793777+00:00
-- url     : https://prove2.me/submissions/c1527fa8-8e6b-4921-bcf2-093ef3efed09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {A B C X : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup X] (f : A →+* B)
    (ρ : B →+* C) (g : Multiplicative X →* B) :
    AddMonoidAlgebra.liftNCRingHom (ρ.comp f) (ρ.toMonoidHom.comp g) (fun _ _ => Commute.all _ _) =
      ρ.comp (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    simp [AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  · intro x
    simp [AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
