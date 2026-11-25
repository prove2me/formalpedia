-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:57.693324+00:00
-- url     : https://prove2.me/submissions/cdbb2a97-3b77-4b74-9867-c2645a603695

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) (a : ι → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ Geo.chartLat (ι := blockIdx n) y a τ) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      (∀ k, (δ k : ℤ) = (τ • a) k + d k) ∧ aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ Geo.chartRingZ (ι := blockIdx n) y c := hs c hc
  obtain ⟨δ', e', he', hv'⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : ι → ℕ := fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * chartMonomial c ex,
    he'.mul (isWeightedHomogeneous_chartMonomial c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv', aeval_chartMonomial, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring
end GroundTheory.Heights₂.Heights.ChartLatSection
