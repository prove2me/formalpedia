-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.compositum_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:30:46.586441+00:00
-- url     : https://prove2.me/submissions/bc035720-5343-4452-b6ca-0a74be70214f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace NormalizedEdge
theorem _root_.solution
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedEdge A F E Q K L)
    (hRight : NormalizedRefinement A F E Q K M) :
    NormalizedRefinement A F E Q L (L ⊔ M) ∧
      NormalizedEdge A F E Q M (L ⊔ M) := by
  induction hRight with
  | refl =>
      rw [sup_eq_left.mpr (hLeft.le A F E Q)]
      exact ⟨.refl, hLeft⟩
  | @tail M N hchain hstep ih =>
      have hsquare := ih.2.compositum A F E Q hstep
      have hsup : (L ⊔ M) ⊔ N = L ⊔ N := by
        rw [sup_assoc, sup_eq_right.mpr (hstep.le A F E Q)]
      rw [hsup] at hsquare
      exact ⟨ih.1.tail hsquare.1, hsquare.2⟩
end NormalizedEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
