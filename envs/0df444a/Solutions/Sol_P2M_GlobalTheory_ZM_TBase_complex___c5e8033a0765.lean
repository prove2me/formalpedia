-- Prove2me | solution 1 for P2M_GlobalTheory_ZM_TBase_complex___c5e8033a0765
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:46.24793+00:00
-- url     : https://prove2.me/submissions/19ca5dd0-15ad-4bce-89a9-552666d7ac25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S S' : Scheme.{0}}
attribute [instance] TObj.grp
variable {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
namespace GlobalTheory.ZM
namespace TBase
theorem _root_.solution (k : ℕ) (hk : k ≠ 0) :
    ((TBase.complex k hk).ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / k) := rfl
end TBase
end GlobalTheory.ZM
