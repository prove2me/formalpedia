-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Multilin_of_found_d47ebe16c976
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:03.903274+00:00
-- url     : https://prove2.me/submissions/cb6e0fb3-8607-44c9-8a5d-ac1de172f68d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_Multilin
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_agree_of_80384e316f32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.Targets
namespace Multilin
theorem _root_.solution
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by
  classical
  intro I hI V n L j a b hV
  have e : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of hBase hCut hEx hDiv I hI V n L' hV
  have hP : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  rw [e, e, e]
  exact hAdd F K ι V hP.multiHomog hP.relevant n (relDim_eq_of_ringKrullDim V n hV.2) L j a b
end Multilin
end GroundTheory.Heights₂.Heights.Targets
