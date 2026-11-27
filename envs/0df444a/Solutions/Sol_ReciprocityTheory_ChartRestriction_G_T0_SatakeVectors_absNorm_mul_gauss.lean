-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.absNorm_mul_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:04:09.951641+00:00
-- url     : https://prove2.me/submissions/8b0f2147-abb7-4eba-80d5-538379bee959

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gaussAbs_eq_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) :
    (Ideal.absNorm (contId G₀) : ℝ) *
      ∏ᶠ w : FinitePlace K, ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) = 1 := by
  have hx : (fun s : G₀.support => G₀.coeff s) ≠ 0 := by
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr h
    intro h0
    exact MvPolynomial.mem_support_iff.mp hs (congrFun h0 ⟨s, hs⟩)
  have := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [finprod_congr (gaussAbs_eq_iSup G₀ h)]
  exact this
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
