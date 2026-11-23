-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.vpt_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:29.809913+00:00
-- url     : https://prove2.me/submissions/12831dd6-17ca-474e-98a7-c69df0d0a46d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_isDominant_jFR

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
  (P : PolAV (Spec (CommRingCat.of V)))
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution {q₁ q₂ : Spec (CommRingCat.of V) ⟶ P.A.left} (h₁ : q₁ ≫ P.A.hom = 𝟙 _)
    (h₂ : q₂ ≫ P.A.hom = 𝟙 _) (h : DegPre.jFR (R := V) F ≫ q₁ = DegPre.jFR (R := V) F ≫ q₂) : q₁ = q₂ := by
  haveI := isDominant_jFR (V := V) F
  haveI : IsProper P.A.hom := P.isAb.proper
  exact ext_of_isDominant_of_isSeparated P.A.hom (h₁.trans h₂.symm) (DegPre.jFR (R := V) F) h
end ReciprocityTheory.ChartRestriction.G.DVR.GC
