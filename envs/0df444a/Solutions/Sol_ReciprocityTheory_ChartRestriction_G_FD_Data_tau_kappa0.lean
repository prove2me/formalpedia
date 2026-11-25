-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.tau_kappa0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:58.817941+00:00
-- url     : https://prove2.me/submissions/ead9a700-6889-4f5e-a712-531602c09b4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_cc_kappa0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by
  have hcc := congrArg τ.1 X.cc_kappa0
  have hconj : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
    rw [← map_neg, ← hcc]
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ.1 X.κ0).symm
  have hre : (τ.1 X.κ0).re = 0 := by
    have h := congrArg Complex.re hconj
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have him := X.κ0_sign τ
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    simp only [Data.c]
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [map_mul, map_neg, norm_mul, map_ofNat]
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have habs : ‖τ.1 X.κ0‖ = -(τ.1 X.κ0).im := by
    conv_lhs => rw [hz]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg him]
  apply Complex.ext
  · simp [hre]
  · simp
    linarith
end ReciprocityTheory.ChartRestriction.G.FD.Data
