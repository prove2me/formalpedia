-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_inv_mem_ad6467638384
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:45.546796+00:00
-- url     : https://prove2.me/submissions/0951d05e-d13f-48b4-b7ec-bf02386796c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134


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
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointAffineChart
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointAffineChart
theorem _root_.solution {m : Ideal (curveRing y)} [m.IsPrime] {e : ℕ} {g : K'} (hg0 : g ≠ 0)
    (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (y ⟨(), t⟩ ^ e / g) ∈ chartRingZ y (fun _ => t) := by
  by_contra hcon
  push Not at hcon
  let R : Subring K' := (chartRingZ y (fun _ => t)).toSubring
  have hBR : curveRing y ≤ R := fun b hb => mem_chart_of_mem_curveRing y hb t ht
  let S' : Submonoid R := m.primeCompl.map (Subring.inclusion hBR)
  let z : R := ⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩
  have hyt : y ⟨(), t⟩ ^ e ≠ 0 := pow_ne_zero _ ht
  have hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hrS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hrS
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K') := congrArg Subtype.val hw
    apply hcon s hs
    rw [← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]
    exact w.2
  obtain ⟨q, hq, hzq, hqS⟩ := Ideal.exists_le_prime_disjoint _ S' hdisj
  obtain ⟨W, hRW, hunit, hlt⟩ := ClosedPointUnitSection.exists_valuationSubring R q
  have hBW : ∀ b : curveRing y, (b : K') ∈ W := fun b => hRW (Subring.inclusion hBR b)
  have hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1 := by
    intro b hb
    apply hunit (Subring.inclusion hBR b)
    intro hbq
    exact Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hW W hBW hBunit t
  have h2 : W.valuation (z : K') < 1 := hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))
  have h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1 := by
    show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1
    field_simp
  have h4 := congrArg W.valuation h3
  rw [map_mul, map_one] at h4
  have h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1 := (W.valuation_le_one_iff _).mpr h1
  have h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2
  exact ne_of_lt h6 h4
end GroundTheory.Heights₂.Heights.ClosedPointAffineChart
