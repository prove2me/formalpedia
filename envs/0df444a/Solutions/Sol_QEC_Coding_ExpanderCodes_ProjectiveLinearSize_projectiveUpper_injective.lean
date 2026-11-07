-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.ProjectiveLinearSize.projectiveUpper_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:45:41.739194+00:00
-- url     : https://prove2.me/submissions/f1ae64ea-1b0c-47be-a044-a0d5062e0cc5

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.ProjectiveLinearSize
open Matrix
variable {K : Type*} [Field K]
namespace QEC.Coding.ExpanderCodes.ProjectiveLinearSize
theorem _root_.solution : Function.Injective (projectiveUpper (K := K)) := by
  intro t u h
  have hPGL :
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (upperUnipotent t)) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (upperUnipotent u)) :=
    congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hPGL
  have h00 := congrArg
    (fun g : Matrix.GeneralLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hc
  change (!![1, t; 0, 1] * Matrix.scalar (Fin 2) (c : K)) 0 0 =
    (!![1, u; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 at h00
  have hcOne : (c : K) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.scalar, Matrix.diagonal] using h00
  have h01 := congrArg
    (fun g : Matrix.GeneralLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  change (!![1, t; 0, 1] * Matrix.scalar (Fin 2) (c : K)) 0 1 =
    (!![1, u; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 1 at h01
  simpa [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.scalar, Matrix.diagonal, hcOne] using h01
end QEC.Coding.ExpanderCodes.ProjectiveLinearSize
