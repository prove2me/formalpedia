-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_pack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:42.439425+00:00
-- url     : https://prove2.me/submissions/8e282f56-5f25-4ac6-bd2c-02196335b072

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hP : Ext.PackingCount) (S : Finset (EuclideanSpace ℂ ι)) (δ ρ : ℝ)
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hS : ∀ a ∈ S, ‖a‖ ≤ ρ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ ‖a - b‖) :
    (S.card : ℝ) ≤ (1 + 4 * ρ / δ) ^ (2 * Fintype.card ι) := by
  have hr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    first
      | rw [Module.finrank_real_of_complex, finrank_euclideanSpace]
      | rw [finrank_real_of_complex, finrank_euclideanSpace]
  let e := ((stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hr)).repr
  let P := S.map ⟨e, e.injective⟩
  have hcard : P.card = S.card := Finset.card_map _
  rcases lt_or_ge ρ (δ / 2) with hsmall | hbig
  · have h1 : S.card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      by_contra hab
      have h3 := hsep a ha b hb hab
      have h2 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      linarith [hS a ha, hS b hb]
    calc (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
      _ ≤ (1 + 4 * ρ / δ) ^ (2 * Fintype.card ι) := by
        refine one_le_pow₀ ?_
        have : 0 ≤ 4 * ρ / δ := by positivity
        linarith
  · have hR : δ ≤ max δ ρ := le_max_left _ _
    have hnorm : ∀ x ∈ P, ‖x‖ ≤ max δ ρ := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      simp only [Function.Embedding.coeFn_mk, LinearIsometryEquiv.norm_map]
      exact (hS a ha).trans (le_max_right _ _)
    have hsep' : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      have hab : a ≠ b := fun h => hxy (by rw [h])
      simp only [Function.Embedding.coeFn_mk, LinearIsometryEquiv.dist_map, dist_eq_norm]
      first
        | exact hsep a ha b hb hab
        | (rw [← map_sub, LinearIsometryEquiv.norm_map]; exact hsep a ha b hb hab)
    have hPc := hP (2 * Fintype.card ι) P δ (max δ ρ) hδ hR hnorm hsep'
    rw [hcard] at hPc
    have hle : 3 * max δ ρ / δ ≤ 1 + 4 * ρ / δ := by
      rw [div_le_iff₀ hδ, add_mul, one_mul, div_mul_cancel₀ _ hδ.ne']
      rcases le_total δ ρ with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        linarith
    refine hPc.trans ?_
    first
      | exact pow_le_pow_left₀ (by positivity) hle _
      | exact pow_le_pow_left (by positivity) hle _
end ReciprocityTheory.ChartRestriction.G.I2
