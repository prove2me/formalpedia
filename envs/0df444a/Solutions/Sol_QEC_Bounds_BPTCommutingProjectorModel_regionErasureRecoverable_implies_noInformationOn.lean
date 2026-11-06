-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_implies_noInformationOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:01:26.873773+00:00
-- url     : https://prove2.me/submissions/0cee99b7-df12-4b19-b342-c72c76c7b0cf

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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_exists_erasureRecovery


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
    (hcorrectable : M.RegionErasureRecoverable region) :
    Semantics.QuditSubsystem.NoInformationOn M.codeSpace (M.regionSubsystem region) := by
  exact ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mpr hcorrectable
end QEC.Bounds.BPTCommutingProjectorModel
