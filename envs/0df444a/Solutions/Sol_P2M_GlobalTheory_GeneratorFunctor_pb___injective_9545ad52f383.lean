-- Prove2me | solution 1 for P2M_GlobalTheory_GeneratorFunctor_pb___injective_9545ad52f383
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:48.975083+00:00
-- url     : https://prove2.me/submissions/6623fd36-6d47-47e1-b2e1-f4d453becaf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) (h : ⊤ ≤ W.ι ⁻¹ᵁ W) :
    Function.Injective (pb W.ι W ⊤ h) := by
  intro x y e
  ext
  have : IsIso (W.ι.appLE W ⊤ h) := by
    rw [Scheme.Opens.ι_appLE]
    have : (homOfLE (show W.ι ''ᵁ ⊤ ≤ W by simp)) = eqToHom (by simp) := rfl
    erw [this]
    rw [eqToHom_op, eqToHom_map]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso (W.ι.appLE W ⊤ h)).1 (congrArg Units.val e)
end GlobalTheory.GeneratorFunctor
