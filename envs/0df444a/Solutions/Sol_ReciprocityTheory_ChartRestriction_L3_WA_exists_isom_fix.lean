-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:52.155445+00:00
-- url     : https://prove2.me/submissions/45c9a7ba-accd-4304-abd4-8e678980ec88

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_quasiRefl_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_quasiRefl_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_quasiRefl_isom
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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨1, Subgroup.one_mem _, rfl, fun v _ _ => rfl⟩
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  obtain ⟨c, hcdef⟩ : ∃ c, c = h (x - y) x := ⟨_, rfl⟩
  have hsum : c + star c = h (x - y) (x - y) := by
    rw [hcdef, hsy]
    simp only [map_sub, LinearMap.sub_apply, hx, hy]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxy
    have : h (x - y) (x - y) = 0 := by rw [← hsum, h0, star_zero, add_zero]
    exact sub_eq_zero.mp (hd _ this)
  have hs0 : star c ≠ 0 := star_ne_zero.mpr hc0
  have ha : c⁻¹ + star c⁻¹ = c⁻¹ * star c⁻¹ * h (x - y) (x - y) := by
    rw [← hsum, star_inv₀]
    field_simp
    ring
  have h1 : quasiRefl h (x - y) c⁻¹ ∘ₗ quasiRefl h (x - y) (star c⁻¹) =
      LinearMap.id := quasiRefl_comp h (x - y) ha
  have h2 : quasiRefl h (x - y) (star c⁻¹) ∘ₗ quasiRefl h (x - y) c⁻¹ =
      LinearMap.id := quasiRefl_comp h (x - y) (by rw [add_comm, ha]; ring)
  refine ⟨LinearEquiv.ofLinear _ _ h1 h2, ?_, ?_, ?_⟩
  · exact fun v w => quasiRefl_isom hs (x - y) ha v w
  · change quasiRefl h (x - y) c⁻¹ x = y
    rw [quasiRefl_apply, ← hcdef, inv_mul_cancel₀ hc0, one_smul, sub_sub_cancel]
  · intro v hxv hyv
    change quasiRefl h (x - y) c⁻¹ v = v
    rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, hxv, hyv, sub_zero, mul_zero,
      zero_smul, sub_zero]
end ReciprocityTheory.ChartRestriction.L3.WA
