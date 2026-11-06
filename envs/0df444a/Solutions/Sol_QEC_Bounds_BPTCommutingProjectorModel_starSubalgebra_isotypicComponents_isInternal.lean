-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.starSubalgebra_isotypicComponents_isInternal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:38:33.559196+00:00
-- url     : https://prove2.me/submissions/d485ac1e-4c33-4e7d-868b-6c5ce959ea89

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_module_isSemisimple

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
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    DirectSum.IsInternal (fun component : isotypicComponents S B => component.1) := by
  classical
  letI : IsSemisimpleModule S B := starSubalgebra_module_isSemisimple S
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp (sSupIndep_isotypicComponents S B)
  · exact (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents S B)
end QEC.Bounds.BPTCommutingProjectorModel
