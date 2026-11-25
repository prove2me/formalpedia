-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:36.103619+00:00
-- url     : https://prove2.me/submissions/77c59bf4-5884-4565-ae1e-d8a34db1ae15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
namespace IntegralSection
theorem _root_.solution {P : ArithVariety n} {a : ι → ℤ}
    (s : IntegralSection P a) {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (hy : ∀ f ∈ P.ideal, aeval y f = 0) (hG : aeval y s.den ≠ 0) :
    aeval y s.num / aeval y s.den ∈ Geo.chartLat (ι := blockIdx n) y a 1 := by
  intro c hc
  have hX : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
    hc k (by simpa using hy _ hk)
  obtain ⟨d, e, ⟨δ, he, hδ⟩, hmem⟩ := s.regular c hX
  have hrel := hy _ hmem
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hrel
  have hmon : aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp [chartMonomial, map_prod]
  rw [hmon] at hrel
  have hpow : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ d k) * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0, hδ k]
    congr 1
    push_cast
    ring
  have hval : aeval y s.num / aeval y s.den * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) =
      aeval y e * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ := by
    rw [hpow, ← mul_assoc, div_mul_eq_mul_div, ← hrel, mul_comm (aeval y s.den), mul_div_assoc,
      div_self hG, mul_one]
  rw [hval]
  exact aeval_div_chart_mem y c hc e δ he
end IntegralSection
end GroundTheory.Heights₂.Heights
