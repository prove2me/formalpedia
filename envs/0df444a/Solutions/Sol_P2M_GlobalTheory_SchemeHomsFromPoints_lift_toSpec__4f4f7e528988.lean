-- Prove2me | solution 1 for P2M_GlobalTheory_SchemeHomsFromPoints_lift_toSpec__4f4f7e528988
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:13.843014+00:00
-- url     : https://prove2.me/submissions/c127fe13-0b57-4c30-b70b-31b0a78d6d45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X : Scheme.{0}} {R : CommRingCat.{0}} (W : X.Opens) (x : Spec R ⟶ X)
    (x' : Spec R ⟶ W) (hx : x' ≫ W.ι = x) (e : ⊤ ≤ x ⁻¹ᵁ W) :
    x' ≫ W.toSpecΓ = Spec.map (x.appLE W ⊤ e ≫ (Scheme.ΓSpecIso R).hom) := by
  have h1 : x.resLE W ⊤ e = (⊤ : (Spec R).Opens).ι ≫ x' := by
    rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, hx]
  have : IsIso (⊤ : (Spec R).Opens).ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  rw [← cancel_epi (⊤ : (Spec R).Opens).ι, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    ← Category.assoc, ← h1, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE]
end GlobalTheory.SchemeHomsFromPoints
