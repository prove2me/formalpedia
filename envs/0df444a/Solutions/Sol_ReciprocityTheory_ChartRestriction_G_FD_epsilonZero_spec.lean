-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.epsilonZero_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:25.782244+00:00
-- url     : https://prove2.me/submissions/9fcb9a0d-ef0d-4647-986f-c58f6ee6b4e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_field_discr_constant_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_one_le_field_half_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_rootDiscriminant_eq_rpow
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 ∧
    ∀ ε, 0 < ε → ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w →
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * ((4 * fdeg E : ℕ) : ℝ)) +
        ((4 * fdeg E : ℕ) : ℝ) + 2 <
        (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) := by
  have hf1 : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  have hd0 : 0 < dE E := field_discr_constant_pos
  have hg0 : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC0 : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  generalize hK : (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) = K2
  have hK1 : 1 ≤ K2 := by
    rw [← hK]
    have : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by positivity
    linarith
  have hN : ((4 * fdeg E : ℕ) : ℝ) = 4 * (fdeg E : ℝ) := by push_cast; ring
  generalize hR : w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * K2 * ((4 * fdeg E : ℕ) : ℝ)) +
      ((4 * fdeg E : ℕ) : ℝ) + 2 = R2
  have hR0 : 0 < R2 := by
    rw [← hR, hN]
    have : 0 ≤ 4 * (fdeg E : ℝ) * Real.log (2 * K2 * (4 * (fdeg E : ℝ))) :=
      mul_nonneg (by linarith) (Real.log_nonneg (by nlinarith))
    linarith
  generalize hB : (X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 = B
  have hB0 : 0 < B := by rw [← hB]; positivity
  have heq : flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w = min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) := by
    rw [← hB, ← hR, ← hK, hN]
    simp only [flowEpsilonBound]
    rw [← rootDiscriminant_eq_rpow]
  rw [heq]
  refine ⟨lt_min one_pos (div_pos (by positivity) (mul_pos hB0 hR0)), min_le_left _ _, fun ε hε hεlt => ?_⟩
  have hle : min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) ≤ (fdeg E : ℝ) ^ 2 / (B * R2) := min_le_right _ _
  have h1 := (le_div_iff₀ (mul_pos hB0 hR0)).1 (le_of_lt (lt_of_lt_of_le hεlt hle))
  rw [lt_div_iff₀ (mul_pos hB0 hε)]
  have hε' : ε * (B * R2) < (fdeg E : ℝ) ^ 2 := by
    have h2 := (lt_div_iff₀ (mul_pos hB0 hR0)).1 (lt_of_lt_of_le hεlt hle)
    exact h2
  calc R2 * (B * ε) = ε * (B * R2) := by ring
    _ < (fdeg E : ℝ) ^ 2 := hε'
end ReciprocityTheory.ChartRestriction.G.FD
