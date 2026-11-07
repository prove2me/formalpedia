-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_index_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:02.029723+00:00
-- url     : https://prove2.me/submissions/6a874e99-ab96-44e4-8c08-8dcffc28e239

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (i j : Option (Fin p)) (D : Matrix (Fin 2) (Fin 2) ℤ)
    (h : lpsHeckeUpperMatrix p i=D*lpsHeckeUpperMatrix p j) : i=j := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h10 h11
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h11
      simp [←h10] at hz
  | some i =>
    cases j with
    | none =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h00
      simp at hz
    | some j =>
      simp [lpsHeckeUpperMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01
      have hz := congrArg (fun x : ℤ => (x : ZMod p)) h01
      have he : (i.val : ZMod p)=(j.val : ZMod p) := by
        simpa [←h00] using hz
      have hv := congrArg ZMod.val he
      have hij : i=j := Fin.ext (by
        simpa only [ZMod.val_cast_of_lt i.isLt,ZMod.val_cast_of_lt j.isLt] using hv)
      exact congrArg some hij
end QEC.Coding.TannerLiftedProduct
