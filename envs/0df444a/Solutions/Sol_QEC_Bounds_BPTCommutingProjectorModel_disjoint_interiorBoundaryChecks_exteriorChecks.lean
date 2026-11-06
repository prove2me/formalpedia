-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorBoundaryChecks_exteriorChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:55:00.807165+00:00
-- url     : https://prove2.me/submissions/4b4cdf94-8222-4342-afbd-ac2e2892ca57

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disjoint_interiorChecks_exteriorChecks

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
    Disjoint (M.interiorChecks region ∪ M.boundaryChecks region) (M.exteriorChecks region) := by
  rw [Finset.disjoint_left]
  intro check hleft hexterior
  rcases Finset.mem_union.mp hleft with hinterior | hboundary
  · exact (Finset.disjoint_left.mp (M.disjoint_interiorChecks_exteriorChecks region))
      hinterior hexterior
  · exact (Finset.mem_sdiff.mp hboundary).2 (Finset.mem_union_right _ hexterior)
end QEC.Bounds.BPTCommutingProjectorModel
