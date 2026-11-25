-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.quasiRefl_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:24.618329+00:00
-- url     : https://prove2.me/submissions/7857447a-2af2-43bb-b3a4-4575d2fef589

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_quasiRefl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
private theorem sesq_smul_right_eq_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h x (c • y) = c * h x y := by
  rw [map_smul, smul_eq_mul]
private theorem sesq_smul_left_eq_star_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h (c • x) y = star c * h x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
private theorem star_apply_eq_apply_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (x y : V) :
    star (h x y) = h y x := by
  have := LinearMap.isSymm_def.mp hs x y
  rwa [starRingEnd_apply] at this
end ReciprocityTheory.ChartRestriction.L3.WA
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  simp only [quasiRefl_apply, map_sub, LinearMap.sub_apply, sesq_smul_left_eq_star_mul,
    sesq_smul_right_eq_mul, star_mul, hsy]
  linear_combination (-(h v u * h u w)) * ha
end ReciprocityTheory.ChartRestriction.L3.WA
