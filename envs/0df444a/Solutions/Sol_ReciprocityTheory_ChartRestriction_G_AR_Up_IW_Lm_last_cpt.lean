-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Lm_last_cpt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:45.445363+00:00
-- url     : https://prove2.me/submissions/fcf50d21-343b-4be8-a049-17a201bd6c24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (z : V (nd X)) (τ : X.Ψ) :
    Lm X (cpt X x0 z) τ (Fin.last r) = 0 := by
  have hN : (mat (nmat X z) τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [mat, nmat]
    · intro a b hab
      have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
      simp [mat, nmat, not_lt.mpr hab'.le, hab'.ne]
  have hNc : ((mat (nmat X z) τ).map (starRingEnd ℂ)).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hN, map_one]
  have key : dmin X.Gm (cpt X x0 z) τ (Fin.last r) = (gram τ.1 X.Gm (mat (cpt X x0 z) τ)).det := rfl
  have e1 : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ := rfl
  have hs : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := fun a => by
    unfold sgn; split_ifs <;> simp
  rw [Lm, key, e1, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul,
    show ∀ A B C D F : Matrix (Fin r) (Fin r) ℂ, A * B * C * (D * F) = A * (B * C * D) * F from
      fun A B C D F => by simp only [Matrix.mul_assoc],
    ← gram_eq_lemma τ.1 X.Gm (mat x0 τ), ho τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hN, hNc, Matrix.det_diagonal]
  simp only [one_mul, mul_one, norm_prod, hs, Finset.prod_const_one, Real.log_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
