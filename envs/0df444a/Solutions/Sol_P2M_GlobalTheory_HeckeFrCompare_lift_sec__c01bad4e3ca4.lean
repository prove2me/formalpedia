-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:55.60255+00:00
-- url     : https://prove2.me/submissions/4ee3a3b5-cfd2-4cf5-87c0-5928dd49ec85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_gx_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Ω : Type} [CommRing Ω]
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (lift (𝟙 (Over.mk x)) (sec' x q hq ≫ a)).left = q ≫ toFib x t a := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst, Category.assoc, toFib_fst, hq]; rfl
  · rw [lift_l_snd, Category.assoc, toFib_snd]; rfl
end GlobalTheory.HeckeFrCompare
