-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.internalBoundary_disjoint_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:48.19434+00:00
-- url     : https://prove2.me/submissions/41356ec0-9bbe-4f2a-9dbc-07fcb8f0a6ca

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
    Disjoint (M.internalBoundary region) (M.exterior region) := by
  rw [Finset.disjoint_left]
  intro site hinternal hexterior
  exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hexterior).1)
    ((Finset.mem_inter.mp hinternal).2)
end QEC.Bounds.BPTCommutingProjectorModel
