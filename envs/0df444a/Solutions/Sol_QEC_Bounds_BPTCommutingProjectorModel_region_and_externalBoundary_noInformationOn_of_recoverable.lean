-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.region_and_externalBoundary_noInformationOn_of_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:54:53.224194+00:00
-- url     : https://prove2.me/submissions/d039d2c1-9687-4dfa-9d21-738115b7b2ec

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn

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
    (hregion : M.RegionErasureRecoverable region)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary region)) :
    Semantics.QuditSubsystem.NoInformationOn M.codeSpace (M.regionSubsystem region) ∧
      Semantics.QuditSubsystem.NoInformationOn M.codeSpace
        (M.regionSubsystem (M.externalBoundary region)) :=
  ⟨M.regionErasureRecoverable_implies_noInformationOn region hregion,
    M.regionErasureRecoverable_implies_noInformationOn (M.externalBoundary region) hexternal⟩
end QEC.Bounds.BPTCommutingProjectorModel
