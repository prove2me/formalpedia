-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.epsilonZero_pos_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:13.47656+00:00
-- url     : https://prove2.me/submissions/63242250-f9c8-440b-9f00-78043bb0194f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ReducedLatticeShortBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryFixingIsotropicPlane
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalShortVectorBoundOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
end Data
private lemma d4ep0_pos_and_le_one (g d f NA NC c1 w : ℝ) (hg : 0 < g) (hd : 0 < d) (hf : 1 ≤ f) (hNC : 0 < NC)
    (hNA : 0 ≤ NA) (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < flowEpsilonBound g d f NA NC c1 w ∧ flowEpsilonBound g d f NA NC c1 w ≤ 1 := by
  unfold flowEpsilonBound
  dsimp only
  refine ⟨lt_min one_pos ?_, min_le_left _ _⟩
  have hH : 0 ≤ NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2) := by positivity
  have hK : 1 ≤ 1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1) := by
    have : 0 ≤ g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) * (2 * c1 + 1) := by
      apply mul_nonneg (mul_nonneg (mul_pos hg (pow_pos hd 2)).le hH)
      linarith
    linarith
  have hL : 0 ≤ Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := Real.log_nonneg (by nlinarith)
  have h4 : 0 ≤ 4 * f * Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := mul_nonneg (by linarith) hL
  apply div_pos (pow_pos (by linarith) 2)
  apply mul_pos (mul_pos (mul_pos (pow_pos (mul_pos hg (pow_pos hd 2)) 2) (pow_pos hNC 2)) hc1)
  linarith
end
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 := by
  have hd : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))
  have hf : (1 : ℝ) ≤ (fdeg E : ℝ) := by
    have h1 : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h3 : 1 ≤ fdeg E := by
      unfold fdeg
      omega
    exact_mod_cast h3
  exact d4ep0_pos_and_le_one _ _ _ _ _ _ _ (Nat.cast_pos.mpr X.g_pos) hd hf (Nat.cast_pos.mpr X.NC_pos) (Nat.cast_nonneg _) hc1 hw1
end ReciprocityTheory.ChartRestriction.G.FD
