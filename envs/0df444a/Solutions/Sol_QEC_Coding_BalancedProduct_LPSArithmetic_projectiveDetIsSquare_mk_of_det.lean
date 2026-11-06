-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_mk_of_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:53:49.427+00:00
-- url     : https://prove2.me/submissions/839e9108-cc4a-418c-863e-75bcd3201280

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_mk_iff

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hpq : (p : ZMod q) ≠ 0)
    (hq : legendreSym q p = 1) :
    ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by
  rw [projectiveDetIsSquare_mk_iff]
  rcases (legendreSym.eq_one_iff' (p := q) (a := p) hpq).mp hq with ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hpq
    simpa [hzero] using hx
  let u : (ZMod q)ˣ := Units.mk0 x hx0
  refine ⟨u, Units.ext ?_⟩
  simpa [u, hdet] using hx
end QEC.Coding.BalancedProduct.LPSArithmetic
