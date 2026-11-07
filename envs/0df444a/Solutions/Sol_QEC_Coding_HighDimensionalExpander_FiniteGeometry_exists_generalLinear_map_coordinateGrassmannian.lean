-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.exists_generalLinear_map_coordinateGrassmannian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:25:57.247553+00:00
-- url     : https://prove2.me/submissions/cbb130ba-bf55-4503-b2a7-8d2663ae5a03

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_exists_linearEquiv_map_coordinateGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (W : FiniteGrassmannian k (Fin d → k) r) :
    ∃ g : GL (Fin d) k,
      (coordinateGrassmannian k d r hr).1.map
          (Matrix.GeneralLinearGroup.toLin g).val = W.1 := by
  obtain ⟨e, he⟩ :=
    exists_linearEquiv_map_coordinateGrassmannian k d r hr W
  let g : GL (Fin d) k := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨g, ?_⟩
  simpa only [g, MulEquiv.apply_symm_apply,
    LinearMap.GeneralLinearGroup.ofLinearEquiv] using he
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
