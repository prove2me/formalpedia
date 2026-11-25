-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.self_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:14.051784+00:00
-- url     : https://prove2.me/submissions/616c8dc7-4769-40b4-a155-22a3ad09fa4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
include he
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution (u : Fin r → ℂ) :
    (hermC τ.1 X.Gm u u).re = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
  have hx := expand X τ e he u
  calc (hermC τ.1 X.Gm u u).re
      = (hermC τ.1 X.Gm u (∑ a : Fin r,
          (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a)).re := by rw [← hx]
    _ = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
      rw [hermC_sum_right, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_right, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
