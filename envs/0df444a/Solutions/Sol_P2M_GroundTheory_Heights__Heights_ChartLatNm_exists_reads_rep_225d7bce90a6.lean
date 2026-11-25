-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_reads_rep_225d7bce90a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:45.540575+00:00
-- url     : https://prove2.me/submissions/76bc73d0-059f-4502-af91-ae3ab38acb2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatNm_isWeightedHomogeneous_chartMono_19c6c68688bb

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
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (hb : Geo.Birational (ι := blockIdx n) y) (c₀ : (k : ι) → Fin (n k + 1))
    (hc₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (b : ι → ℤ) (s : Ω) :
    ∃ (f q : MvPolynomial (Coord n) ℤ) (δf δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) f δf ∧
      IsWeightedHomogeneous (coordDeg n) q δq ∧ (∀ k, (δf k : ℤ) = δq k + b k) ∧ aeval y q ≠ 0 ∧
      aeval y f = s * aeval y q := by
  obtain ⟨g, q, d, hg, hq, hq0, he⟩ := exists_rep y hb (s * ∏ k, y ⟨k, c₀ k⟩ ^ (-b k))
  refine ⟨g * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (b k).toNat,
    q * ∏ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ^ (-b k).toNat, d + fun k => (b k).toNat,
    d + fun k => (-b k).toNat, hg.mul (isWeightedHomogeneous_chartMono c₀ _),
    hq.mul (isWeightedHomogeneous_chartMono c₀ _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    exact mul_ne_zero hq0 (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k))
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he]
    have h1 : (∏ k, y ⟨k, c₀ k⟩ ^ (-b k)) * ∏ k, y ⟨k, c₀ k⟩ ^ (b k).toNat =
        ∏ k, y ⟨k, c₀ k⟩ ^ (-b k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc₀ k)]
      congr 1
      omega
    linear_combination (s * aeval y q) * h1
end GroundTheory.Heights₂.Heights.ChartLatNm
