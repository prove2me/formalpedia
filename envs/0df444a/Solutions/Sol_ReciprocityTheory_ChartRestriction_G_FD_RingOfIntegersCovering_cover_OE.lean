-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering.cover_OE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:25.945523+00:00
-- url     : https://prove2.me/submissions/2780a59d-d142-4712-a5ce-3942fe8bef49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RingOfIntegersCovering
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BabaiCovering_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_card_complexPlaces_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_dE_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_inner_bas_bd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_norm_bd_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_card_CP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_finrank_VS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_mem_span_bas


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
theorem _root_.solution (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
  set f : ℝ := (Fintype.card (CP E) : ℝ) with hf_def
  have hf : 0 < f := Nat.cast_pos.mpr card_complexPlaces_pos
  set D := dE E with hD_def
  have hD : 0 < D := dE_pos
  set t := D ^ (1 / f) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hD _
  have htinv : D ^ (-(1 / f)) = t⁻¹ := Real.rpow_neg hD.le _
  set lam := Real.sqrt (4 * f * t⁻¹) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = 4 * f * t⁻¹ := Real.sq_sqrt (by positivity)
  have hmin : ∀ x ∈ span ℤ (Set.range (bd E)), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have h := norm_bd_ge x hx hx0
    rw [← hf_def, ← hD_def, htinv] at h
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt h
  obtain ⟨x, hx, hxb⟩ := BabaiCovering.cover (bas E) (bd E) inner_bas_bd lam hlam hmin Z
  obtain ⟨α, rfl⟩ := mem_span_bas hx
  refine ⟨α, ?_⟩
  have hn : (finrank ℝ (VS E) : ℝ) = 2 * f := by
    rw [finrank_VS, (card_CP (E := E)).2]
    push_cast
    ring
  have hfdeg : (fdeg E : ℝ) = f := by rw [← (card_CP (E := E)).1]
  have hrd : rdE E ^ 2 = t := by
    rw [rdE, ← hD_def, (card_CP (E := E)).2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    rw [← hf_def]
    field_simp
  rw [hn] at hxb
  have hbound : (2 * f) / 4 * ((2 * f) ^ 2 / lam) ^ 2 = 2 * f ^ 4 * t := by
    rw [div_pow, hlam2]
    field_simp
    ring
  rw [hbound] at hxb
  have hB : 0 ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num : (2 : ℕ) ≠ 0)]
  calc ‖Z - iota E (α : E)‖ ^ 2 ≤ 2 * f ^ 4 * t := hxb
    _ ≤ 4 * f ^ 4 * t := by nlinarith [pow_pos hf 4]
    _ = (2 * (fdeg E : ℝ) ^ 2 * rdE E) ^ 2 := by
        rw [mul_pow, mul_pow, hrd, hfdeg]
        ring
end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
