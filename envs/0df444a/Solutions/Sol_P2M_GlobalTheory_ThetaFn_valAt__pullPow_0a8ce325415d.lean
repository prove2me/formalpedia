-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:31.110568+00:00
-- url     : https://prove2.me/submissions/5d7cf3d8-1a00-44bc-a4e6-bb8411d1a69f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] [Unique K]
  [Unique K']
namespace GlobalTheory.ThetaFn
theorem _root_.solution {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) (x : Sp ℂ ⟶ Z) (j : K' → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K' => ψ) j) :
    valAt' x (LB.wchart L (fun _ : K' => ψ) j) ((pullPow L (K' := K') h e a s).f j) =
      valAt' (x ≫ h) (LB.wchart L (fun _ : K => φ) (fun _ => j default))
        (s.f (fun _ => j default)) :=
  valAt'_appLE' x h _ hj _
end GlobalTheory.ThetaFn
