-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.interior_disjoint_externalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:47.283113+00:00
-- url     : https://prove2.me/submissions/8ea94c03-50f9-4e83-adcc-c9d57d7d90d4

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_externalBoundary_iff


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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interior region) (M.externalBoundary region) := by
  rw [Finset.disjoint_left]
  intro site hinterior hexternal
  exact (M.mem_externalBoundary_iff region site).mp hexternal |>.1
    ((Finset.mem_sdiff.mp hinterior).1)
end QEC.Bounds.BPTCommutingProjectorModel
