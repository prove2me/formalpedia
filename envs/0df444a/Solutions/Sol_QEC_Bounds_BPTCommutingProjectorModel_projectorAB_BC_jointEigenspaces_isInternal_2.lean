-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BC_jointEigenspaces_isInternal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:51:57.327296+00:00
-- url     : https://prove2.me/submissions/4f7abbdd-0189-499a-bc2e-64e78851534d

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

namespace QBAux

theorem projector_isSelfAdjoint (M : BPTCommutingProjectorModel L kappa) (c : kappa) :
    IsSelfAdjoint (M.projector c) := by
  show star (M.projector c) = M.projector c
  rw [LinearMap.star_eq_adjoint]
  exact M.projector_self_adjoint c

theorem projectorProductOn_insert (M : BPTCommutingProjectorModel L kappa) (a : kappa)
    (s : Finset kappa) (ha : a ∉ s) :
    M.projectorProductOn (insert a s) = M.projector a * M.projectorProductOn s := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  exact Finset.noncommProd_insert_of_notMem s a M.projector _ ha

theorem projector_commute_projectorProductOn (M : BPTCommutingProjectorModel L kappa)
    (c : kappa) (s : Finset kappa) :
    Commute (M.projector c) (M.projectorProductOn s) := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  exact Finset.noncommProd_commute s M.projector _ _ (fun x _ => M.projector_commute c x)

theorem projectorProductOn_isSelfAdjoint (M : BPTCommutingProjectorModel L kappa)
    (s : Finset kappa) : IsSelfAdjoint (M.projectorProductOn s) := by
  induction s using Finset.induction_on with
  | empty =>
      unfold BPTCommutingProjectorModel.projectorProductOn
      simp only [Finset.noncommProd_empty]
      exact IsSelfAdjoint.one _
  | insert a s ha ih =>
      rw [projectorProductOn_insert M a s ha]
      exact ((projector_isSelfAdjoint M a).commute_iff ih).mp
        (projector_commute_projectorProductOn M a s)

theorem projectorProductOn_commute (M : BPTCommutingProjectorModel L kappa)
    (s t : Finset kappa) : Commute (M.projectorProductOn s) (M.projectorProductOn t) := by
  unfold BPTCommutingProjectorModel.projectorProductOn
  apply Finset.noncommProd_commute
  intro x _
  exact (projector_commute_projectorProductOn M x s).symm

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region) eigenvalue.1) := by
  have hA : (M.projectorAB region).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (QBAux.projectorProductOn_isSelfAdjoint M _)
  have hB : (M.projectorBC region).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (QBAux.projectorProductOn_isSelfAdjoint M _)
  exact LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB
    (QBAux.projectorProductOn_commute M _ _)
