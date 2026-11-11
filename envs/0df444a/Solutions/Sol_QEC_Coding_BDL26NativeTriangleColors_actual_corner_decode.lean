-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.actual_corner_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:28:47.591836+00:00
-- url     : https://prove2.me/submissions/be193b5c-3b65-42c1-b52d-f0cbe7227e66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
section
namespace QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
namespace G
export BDL26NativePresentationGenerator (Code)
end G
open G
noncomputable section Semantic
variable (P : TannerSquarePresentation) (key : Triangle P → ℕ)
end Semantic
noncomputable section Actual
open scoped Classical
private theorem corners_at (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    tripleAt (corners S n t) i=BDL26NativePresentationGenerator.generatedVertexIndex S n
      (triangleVertex (P S n) t i) := by
  fin_cases i <;> rfl
end Actual
end QEC.Coding.BDL26NativeTriangleColors
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    BDL26NativeStateRows.decode S n (tripleAt (corners S n t) i)=triangleVertex (P S n) t i := by
  rw [corners_at]
  exact Equiv.symm_apply_apply (BDL26NativePresentationGenerator.generatedVertexIndex S n) _
end QEC.Coding.BDL26NativeTriangleColors
