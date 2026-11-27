-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing__SpecIso_hom_constUnit_5049c202e200
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:50.875371+00:00
-- url     : https://prove2.me/submissions/f9610d43-61d5-46b3-b33b-679f43ba1d3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (constUnit R F ζ : Γ((TFK (R := R) F).left, ⊤)) = (ζ : F) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (ζ : F)
end GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
