-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.normSq_det_orthogonalFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:51.062569+00:00
-- url     : https://prove2.me/submissions/23128bf7-731b-4528-b8da-c9e66468632d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem det_gram' (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    (ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M).det = M.det * (X.Gm.map τ.1).det * (starRingEnd ℂ) M.det := by
  have e : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    first
    | exact Finset.sum_comm
    | rw [Finset.sum_comm]
  have hc : (M.map (starRingEnd ℂ)).det = (starRingEnd ℂ) M.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
private theorem norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    ‖(mat x0 τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x0 τ).det‖ = 1 := by
  have h := congrArg Matrix.det (hx0 τ)
  rw [det_gram', Matrix.det_diagonal] at h
  have hn : ‖(mat x0 τ).det * (X.Gm.map τ.1).det * (starRingEnd ℂ) (mat x0 τ).det‖ = 1 := by
    rw [h, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sgn
    split_ifs <;> simp
  rwa [norm_mul, norm_mul, Complex.norm_conj] at hn
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (τ : X.Ψ) :
    Complex.normSq (mat x0 τ).det * ‖(X.Gm.map τ.1).det‖ = 1 := by
  rw [Complex.normSq_eq_norm_sq, ← norm_det_mat_mul_norm_det_Gm_mul_norm_det_eq_one X hx0 τ]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
