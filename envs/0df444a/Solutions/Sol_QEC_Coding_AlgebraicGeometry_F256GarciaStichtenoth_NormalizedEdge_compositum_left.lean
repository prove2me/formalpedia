-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.compositum_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:27:46.312225+00:00
-- url     : https://prove2.me/submissions/7884f7c5-7e38-44a2-b500-0a00e2beb786

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_in_subfield_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_adjoin_add_algebraMap_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticCompositumCell_normalized_weakDifferent_or_redundant
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_IntermediateIntegralModels_modelResidueFieldFinite


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
    (hRight : NormalizedEdge A F E Q K M) :
    NormalizedEdge A F E Q L (L ⊔ M) := by
  have hKL := hLeft.le A F E Q
  have hKM := hRight.le A F E Q
  letI : Fact (K ≤ L) := ⟨hKL⟩
  letI : Fact (K ≤ M) := ⟨hKM⟩
  let U := L ⊔ M
  letI : Fact (K ≤ U) := ⟨hKL.trans le_sup_left⟩
  letI : Fact (L ≤ U) := ⟨le_sup_left⟩
  obtain ⟨a, y, hy, ha, hL⟩ := hLeft
  obtain ⟨b, z, hz, hb, hM⟩ := hRight
  have hyL : y ∈ L := by
    rw [← hL]
    exact IntermediateField.mem_adjoin_simple_self K y
  have hzM : z ∈ M := by
    rw [← hM]
    exact IntermediateField.mem_adjoin_simple_self K z
  have hzU : z ∈ U := (show M ≤ U from le_sup_right) hzM
  have hU : (L⟮z⟯).restrictScalars F = U := by
    change (L⟮z⟯).restrictScalars F = L ⊔ M
    rw [← hM, IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.restrictScalars_adjoin_eq_sup, ← sup_assoc,
      sup_eq_left.mpr hKL]
  let yL : L := ⟨y, hyL⟩
  let zU : U := ⟨z, hzU⟩
  have hyEq : yL ^ 2 + yL = algebraMap K L a := by
    apply Subtype.ext
    exact hy
  have hzEq : zU ^ 2 + zU = algebraMap K U b := by
    apply Subtype.ext
    exact hz
  letI : Finite (heightOnePlace (k := F256) (K := K) (P K)).residueField :=
    IntermediateIntegralModels.modelResidueFieldFinite A F E K (P K)
  obtain ⟨c, hc, heq, _, _⟩ :=
    quadraticCompositumCell_normalized_weakDifferent_or_redundant
      A (C K) (C L) (C U) K L U (P K) (P L) (P U) a b yL zU
      hyEq hzEq (adjoin_in_subfield_eq_top K L y hyL hL)
      (adjoin_in_subfield_eq_top L U z hzU hU) ha hb
  refine ⟨algebraMap K L b + c ^ 2 + c, z + (c : E), ?_, hc, ?_⟩
  · exact congrArg (fun t : U => (t : E)) heq
  · change (L⟮z + algebraMap L E c⟯).restrictScalars F = U
    rw [adjoin_add_algebraMap_eq, hU]
end NormalizedEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
