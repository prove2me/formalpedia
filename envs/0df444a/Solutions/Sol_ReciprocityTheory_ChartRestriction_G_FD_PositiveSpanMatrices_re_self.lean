-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.re_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:22.056681+00:00
-- url     : https://prove2.me/submissions/d79282ca-4b9d-47ee-8e3b-92c65d3784eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ortho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_quad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (y : Fin r → ℂ) :
    (hermC τ.1 X.Gm y y).re = ∑ c : Fin r, sgn X.p0 (c : ℕ) * ‖hermC τ.1 X.Gm y (col (mat x τ) c)‖ ^ 2 := by
  have hs : ∀ c : Fin r, sgn X.p0 c * sgn X.p0 c = 1 := by
    intro c
    unfold sgn
    split_ifs <;> norm_num
  conv_lhs => rw [expand X hx τ hdet y]
  rw [hermC_quad]
  simp_rw [ortho_apply X hx τ]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_mul, Complex.conj_ofReal]
  have e : ((sgn X.p0 c : ℝ) : ℂ) * hermC τ.1 X.Gm y (col (mat x τ) c) * ((sgn X.p0 c : ℝ) : ℂ) *
      (((sgn X.p0 c : ℝ) : ℂ) * conj (hermC τ.1 X.Gm y (col (mat x τ) c))) =
      ((sgn X.p0 c * sgn X.p0 c * sgn X.p0 c * Complex.normSq (hermC τ.1 X.Gm y (col (mat x τ) c)) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj]
    ring
  rw [e, Complex.ofReal_re, hs, one_mul, Complex.normSq_eq_norm_sq]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
