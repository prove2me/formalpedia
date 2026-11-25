-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:18.339011+00:00
-- url     : https://prove2.me/submissions/5de14d43-cc91-4d0a-ba4c-279928014816

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (μ : ℂ)
    (hμ : μ ≠ 0) (h : segre z = μ • segre z') : SameOrbit z z' := by
  classical
  choose p0 hp0 using hz'
  have hz0 : ∀ k, z ⟨k, p0 k⟩ ≠ 0 := by
    have hs : segre z p0 ≠ 0 := by
      rw [h, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ (Finset.prod_ne_zero_iff.mpr fun k _ => hp0 k)
    intro k hk
    exact hs (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hR : ∀ k, ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hz0 l
  have hR' : ∀ k, ∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hp0 l
  refine ⟨fun k => μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩,
    fun k => div_ne_zero (mul_ne_zero hμ (hR' k)) (hR k), ?_⟩
  funext q
  obtain ⟨k, i⟩ := q
  have e := congrFun h (Function.update p0 k i)
  rw [Pi.smul_apply, smul_eq_mul, segre_update, segre_update] at e
  show z ⟨k, i⟩ = μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / (∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩) * z' ⟨k, i⟩
  field_simp [hR k]
  linear_combination e
end ReciprocityTheory.ChartRestriction.G.Geo
