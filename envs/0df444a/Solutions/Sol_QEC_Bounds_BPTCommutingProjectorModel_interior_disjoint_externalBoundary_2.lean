-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.interior_disjoint_externalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:51:56.355594+00:00
-- url     : https://prove2.me/submissions/da75d826-8238-4226-b520-1f2ef0761d61

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
    Disjoint (M.interior region) (M.externalBoundary region) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [BPTCommutingProjectorModel.interior, BPTCommutingProjectorModel.externalBoundary,
    Finset.mem_sdiff] at hx hy
  exact hy.2 hx.1
