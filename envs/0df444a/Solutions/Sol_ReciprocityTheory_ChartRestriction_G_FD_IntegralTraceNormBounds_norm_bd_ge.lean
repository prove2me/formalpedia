-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.norm_bd_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:12.640528+00:00
-- url     : https://prove2.me/submissions/1875b541-4da8-4190-a9c5-bccd5a02ced3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_trace_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_norm_discr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_prod_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_dE_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralTraceNormBounds_card_complexPlaces_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_norm_sq_iota


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
theorem _root_.solution (x : VS E) (hx : x ∈ span ℤ (Set.range (bd E))) (hx0 : x ≠ 0) :
    4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  obtain ⟨β, hβdef⟩ : ∃ β : E, β = ∑ j, c j • ed E j := ⟨_, rfl⟩
  have hxβ : x = iota E (2 * cc β) := by
    rw [← hc, hβdef]
    simp only [bd, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
  have hβ0 : β ≠ 0 := by
    rintro h
    apply hx0
    rw [hxβ, h, cc, map_zero, mul_zero, map_zero]
  have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
    intro γ
    rw [hβdef]
    exact trace_int c γ
  have hN := norm_discr β hβ0 hint
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
    rw [hxβ, norm_sq_iota, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
      map_ofNat, h2n]
    ring
  have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
  have hd : 0 < dE E := dE_pos
  have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
    (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  rw [Real.finset_prod_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
  have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
      |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
  rw [hnorm]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
    (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
  calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
      ≤ 4 * (Fintype.card (CP E) : ℝ) *
        (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
    _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
