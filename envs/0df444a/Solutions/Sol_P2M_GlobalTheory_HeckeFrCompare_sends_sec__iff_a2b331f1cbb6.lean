-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeFrCompare_sends_sec__iff_a2b331f1cbb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:55.721995+00:00
-- url     : https://prove2.me/submissions/0743079f-0447-42c6-93ee-baaa266e5edc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_iff
import Theorems.Thm_P2M_GlobalTheory_HeckeFrCompare_lift_sec__c01bad4e3ca4

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
theorem _root_.solution {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
    (hψ : ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) (b : Over.mk x' ⟶ Xo.univ.t.G) :
    Sends ψ (sec' x q hq ≫ a) b ↔ q ≫ push ψ t a = b.left := by
  rw [sends_iff hψ, lift_sec', push, Category.assoc]
end GlobalTheory.HeckeFrCompare
