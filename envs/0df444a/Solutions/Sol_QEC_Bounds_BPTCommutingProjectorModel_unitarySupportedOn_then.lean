-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:55:28.124429+00:00
-- url     : https://prove2.me/submissions/3a593867-8c1f-48e5-bae9-27be79228c24

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_localExtension_comp


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn region U) (hV : M.UnitarySupportedOn region V) :
    M.UnitarySupportedOn region (thenUnitary U V) := by
  rcases hU with ⟨localU, hlocalU⟩
  rcases hV with ⟨localV, hlocalV⟩
  refine ⟨localV.comp localU, ?_⟩
  change (M.regionSubsystem region).extendLocalToRegister (localV.comp localU) =
    V.toLinearEquiv.toLinearMap.comp U.toLinearEquiv.toLinearMap
  rw [← localExtension_comp, hlocalV, hlocalU]
end QEC.Bounds.BPTCommutingProjectorModel
