-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.gram_commutes_of_star_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:40:40.681993+00:00
-- url     : https://prove2.me/submissions/7065e4ec-155b-4aca-8f18-ace84641ae63

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_intertwines_of_star

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
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (f : H →ₗ[Complex] K)
    (hintertwines : ∀ r, f.comp (rhoH r) = (rhoK r).comp f)
    (r : R) :
    Commute (f.adjoint.comp f) (rhoH r) := by
  have hadjoint := adjoint_intertwines_of_star rhoH rhoK hH hK f hintertwines r
  change (f.adjoint.comp f).comp (rhoH r) =
    (rhoH r).comp (f.adjoint.comp f)
  calc
    (f.adjoint.comp f).comp (rhoH r) =
        f.adjoint.comp (f.comp (rhoH r)) := by rw [LinearMap.comp_assoc]
    _ = f.adjoint.comp ((rhoK r).comp f) := by rw [hintertwines r]
    _ = (f.adjoint.comp (rhoK r)).comp f := by rw [← LinearMap.comp_assoc]
    _ = ((rhoH r).comp f.adjoint).comp f := by rw [hadjoint]
    _ = (rhoH r).comp (f.adjoint.comp f) := by rw [LinearMap.comp_assoc]
end QEC.Bounds.BPTCommutingProjectorModel
