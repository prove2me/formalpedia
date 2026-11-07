-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominant_inv_first_entry_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:47:39.324545+00:00
-- url     : https://prove2.me/submissions/4bd8e5e7-8368-4a5a-879e-a28f9e1c8713

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {k : Type u} [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    ((((dominantGeneralLinear k weight.toDominant)⁻¹ :
      GL (Fin (n + 1)) (LocalFunctionField k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) 0 0).orderTop =
      ((-(weight.toDominant.exponent (0 : Fin (n + 1)) : ℤ) : ℤ) :
        WithTop ℤ) := by
  change (((uniformizerUnit k ^
    weight.toDominant.exponent (0 : Fin (n + 1)))⁻¹ :
      Units (LocalFunctionField k)) : LocalFunctionField k).orderTop = _
  exact orderTop_uniformizerUnit_pow_inv _
end QEC.Coding.HighDimensionalExpander.SphericalHecke
