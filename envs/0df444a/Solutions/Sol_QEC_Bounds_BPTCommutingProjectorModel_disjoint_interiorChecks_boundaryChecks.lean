-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_boundaryChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:18.407301+00:00
-- url     : https://prove2.me/submissions/04cad47d-eecf-4267-ba76-849c8da87c80

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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.interiorChecks region) (M.boundaryChecks region) := by
  rw [Finset.disjoint_left]
  intro check hinterior hboundary
  exact (Finset.mem_sdiff.mp hboundary).2 (Finset.mem_union_left _ hinterior)
end QEC.Bounds.BPTCommutingProjectorModel
