-- Prove2me | solution 1 for P2M_GlobalTheory_KS_VertField_valAt__comp_3a1fda3a8496
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:21.074801+00:00
-- url     : https://prove2.me/submissions/28e14406-2a0c-4b9b-bd68-494a4c31d789

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorField

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertField
namespace GlobalTheory.KS.VertField
theorem _root_.solution {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  have hpre : (x ≫ φ) ⁻¹ᵁ U = x ⁻¹ᵁ φ ⁻¹ᵁ U := by simp
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · rw [dif_pos (by rwa [hpre]), dif_pos h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dif_neg (by rwa [hpre]), dif_neg h]
end GlobalTheory.KS.VertField
