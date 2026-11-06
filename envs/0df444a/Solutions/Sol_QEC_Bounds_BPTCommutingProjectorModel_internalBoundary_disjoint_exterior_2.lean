-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.internalBoundary_disjoint_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:08:55.512499+00:00
-- url     : https://prove2.me/submissions/aebd791f-5336-42e5-9a64-36eb1de6422e

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

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Disjoint (M.internalBoundary region) (M.exterior region) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [BPTCommutingProjectorModel.exterior, BPTCommutingProjectorModel.internalBoundary,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl] at hx hy
  exact hy.1 hx.2
