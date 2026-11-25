-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.quasiRefl_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:20.082201+00:00
-- url     : https://prove2.me/submissions/92216879-ffe4-45d8-870a-4b5f13b3c709

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
end ReciprocityTheory.ChartRestriction.L3.WA
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, quasiRefl_apply, quasiRefl_apply, LinearMap.id_apply,
    map_sub, sesq_smul_right_eq_mul, sub_sub, ← add_smul]
  have hc : b * h u v + a * (h u v - b * h u v * h u u) = 0 := by
    linear_combination (h u v) * hab
  rw [hc, zero_smul, sub_zero]
end ReciprocityTheory.ChartRestriction.L3.WA
