-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:37.880817+00:00
-- url     : https://prove2.me/submissions/046b930a-5ac2-43ff-a1bd-131a4e9865c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.ThetaFn
theorem _root_.solution {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) (k : ℤ) :
    valAt' x U (f ^ k).val = valAt' x U f.val ^ k := by
  simp only [valAt'_eq_valHom x h]
  have h1 : ∀ v : Γ(X, U)ˣ, valHom x U h v.val =
      ((Units.coeHom ℂ).comp (Units.map (valHom x U h).toMonoidHom)) v := fun v => rfl
  simp only [h1, map_zpow]
end GlobalTheory.ThetaFn
