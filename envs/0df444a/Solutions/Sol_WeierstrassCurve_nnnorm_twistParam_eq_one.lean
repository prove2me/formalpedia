-- Prove2me | solution 1 for WeierstrassCurve.nnnorm_twistParam_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/abab6a55-7951-58c6-b951-ff972b1aa2ef

import Definitions.Def_TateCurve_QSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_nnnorm_twistParam_eq_one

open scoped NNReal
open IsUltrametricDist

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "c_relation c₆ Δ c₄"
p2m_open "WeierstrassCurve"
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem nnnorm_c₆_eq_one_of_nnnorm_c₄_eq_one (E : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) : ‖E.c₆‖₊ = 1 := by
  have hrel : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  have h1728 : ‖(1728 : K) * E.Δ‖₊ < 1 := by
    have hint : ‖(1728 : K)‖₊ ≤ 1 := by exact_mod_cast nnnorm_natCast_le_one K 1728
    calc ‖(1728 : K) * E.Δ‖₊ = ‖(1728 : K)‖₊ * ‖E.Δ‖₊ := nnnorm_mul _ _
      _ ≤ 1 * ‖E.Δ‖₊ := by gcongr
      _ = ‖E.Δ‖₊ := one_mul _
      _ < 1 := hΔ
  have key : ‖E.c₆‖₊ ^ 2 = 1 := by
    have hane : ‖E.c₄ ^ 3‖₊ ≠ ‖-((1728 : K) * E.Δ)‖₊ := by
      rw [nnnorm_pow, hc₄, one_pow, nnnorm_neg]; exact (ne_of_lt h1728).symm
    calc ‖E.c₆‖₊ ^ 2 = ‖E.c₆ ^ 2‖₊ := (nnnorm_pow _ _).symm
      _ = ‖E.c₄ ^ 3 + -((1728 : K) * E.Δ)‖₊ := by rw [hrel, sub_eq_add_neg]
      _ = max ‖E.c₄ ^ 3‖₊ ‖-((1728 : K) * E.Δ)‖₊ := nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hane
      _ = 1 := by rw [nnnorm_pow, hc₄, one_pow, nnnorm_neg]; exact max_eq_left h1728.le
  rcases le_total ‖E.c₆‖₊ 1 with h | h
  · refine le_antisymm h ?_
    calc (1 : ℝ≥0) = ‖E.c₆‖₊ ^ 2 := key.symm
      _ = ‖E.c₆‖₊ * ‖E.c₆‖₊ := pow_two _
      _ ≤ ‖E.c₆‖₊ * 1 := by gcongr
      _ = ‖E.c₆‖₊ := mul_one _
  · refine le_antisymm ?_ h
    calc ‖E.c₆‖₊ = ‖E.c₆‖₊ * 1 := (mul_one _).symm
      _ ≤ ‖E.c₆‖₊ * ‖E.c₆‖₊ := by gcongr
      _ = ‖E.c₆‖₊ ^ 2 := (pow_two _).symm
      _ = 1 := key

end WeierstrassCurve

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    (E E' : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) (hc₄' : ‖E'.c₄‖₊ = 1) (hΔ' : ‖E'.Δ‖₊ < 1) :
    ‖E.c₆ * E'.c₄ / (E'.c₆ * E.c₄)‖₊ = 1 := by
  rw [nnnorm_div, nnnorm_mul, nnnorm_mul,
    WeierstrassCurve.nnnorm_c₆_eq_one_of_nnnorm_c₄_eq_one E hc₄ hΔ,
    WeierstrassCurve.nnnorm_c₆_eq_one_of_nnnorm_c₄_eq_one E' hc₄' hΔ', hc₄, hc₄']
  norm_num

end S_WeierstrassCurve_nnnorm_twistParam_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_nnnorm_twistParam_eq_one (solution)
