-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.disjoint_interiorChecks_exteriorChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:52:12.273869+00:00
-- url     : https://prove2.me/submissions/35145b0c-e9c2-4d2e-878b-c7a603a2eec8

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
    Disjoint (M.interiorChecks region) (M.exteriorChecks region) := by
  rw [Finset.disjoint_left]
  intro check hinterior hexterior
  rcases (Finset.mem_filter.mp hinterior).2 with ⟨inside, hinside⟩
  rcases (Finset.mem_filter.mp hexterior).2 with ⟨outside, houtside⟩
  have hsuppInside : inside ∈ M.support check := (Finset.mem_inter.mp hinside).1
  have hinteriorInside : inside ∈ M.interior region := (Finset.mem_inter.mp hinside).2
  have hsuppOutside : outside ∈ M.support check := (Finset.mem_inter.mp houtside).1
  have hexteriorOutside : outside ∈ M.exterior region := (Finset.mem_inter.mp houtside).2
  have hsubset := M.support_subset_region_of_mem_interior region check hsuppInside hinteriorInside
  exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hexteriorOutside).1)
    (hsubset hsuppOutside)
end QEC.Bounds.BPTCommutingProjectorModel
