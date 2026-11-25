-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.posDef_int_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:34.912027+00:00
-- url     : https://prove2.me/submissions/b70a46d2-b474-4cbb-af5f-ff11347f5596

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC
theorem _root_.solution {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let q : (Fin N → ℝ) → ℝ := fun y => y ⬝ᵥ (A *ᵥ y)
  have hqc : Continuous q :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y := by
    intro y hy
    have h0 := hA.dotProduct_mulVec_pos hy
    simpa [q] using h0

  obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy0
    exact zero_ne_one hy0
  refine ⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖ := by
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    calc (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by rw [Real.norm_eq_abs]; exact h1
      _ ≤ ‖(fun i => (x i : ℝ))‖ := norm_le_pi_norm (fun i => (x i : ℝ)) i
  set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr
  have hs0 : ‖xr‖ ≠ 0 := (lt_of_lt_of_le one_pos hs1).ne'
  have hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  have hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr) := by
    simp only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have h3 : q y0 ≤ q (‖xr‖⁻¹ • xr) := hmin hy
  have h4 : 0 < q y0 := hpos y0 hy0ne
  have hs2 : 1 ≤ ‖xr‖ ^ 2 := by nlinarith
  show q y0 ≤ q xr
  rw [hq]
  nlinarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC
