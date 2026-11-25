-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:19:18.471314+00:00
-- url     : https://prove2.me/submissions/644d36b4-f1f5-459f-9117-85cbd169da7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_u_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dOf_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_dOf_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_abs_re_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.IsOrtho (rmul x (bOf X x)) := by
  intro τ
  change gram τ.1 X.Gm (mat x τ * (uOf X x τ * Matrix.diagonal (sOf X x τ))) = _
  rw [← Matrix.mul_assoc, gram_mul, gram_u_eq X hx τ, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  have hd : dOf X x τ a = ((dOf X x τ a).re : ℂ) :=
    Complex.ext (by simp) (by simp [dOf_real X hx τ a])
  have hpos := sgn_dOf_pos X hx τ a
  have habs := abs_re_pos X hx τ a
  rw [hd]
  simp only [sOf, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  set d := (dOf X x τ a).re
  have hs : (Real.sqrt |d|)⁻¹ * d * (Real.sqrt |d|)⁻¹ = d / |d| := by
    rw [mul_comm _ d, mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_mul_inv]
  rw [hs]
  rcases sgn_sq X.p0 a with h1 | h1 <;> rw [h1] at hpos ⊢
  · rw [abs_of_pos (by linarith), div_self (by linarith)]
  · have hn : d < 0 := by linarith
    rw [abs_of_neg hn, div_neg, div_self hn.ne]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
