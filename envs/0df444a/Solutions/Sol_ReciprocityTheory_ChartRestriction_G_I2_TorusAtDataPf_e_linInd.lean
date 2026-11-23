-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.e_linInd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:32.356373+00:00
-- url     : https://prove2.me/submissions/45c2048c-e4fa-41b0-808f-776d82c70121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sgn_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_pair_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left


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
theorem _root_.solution : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := pair_sum X τ e he g Finset.univ i
  rw [hg, hermC_zero_left, if_pos (Finset.mem_univ i)] at h1
  have h2 := sgn_sq X i
  calc g i = g i * (((sgn X.p0 i : ℝ) : ℂ) * ((sgn X.p0 i : ℝ) : ℂ)) := by rw [h2, mul_one]
    _ = (g i * ((sgn X.p0 i : ℝ) : ℂ)) * ((sgn X.p0 i : ℝ) : ℂ) := by ring
    _ = 0 := by rw [← h1, zero_mul]
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
