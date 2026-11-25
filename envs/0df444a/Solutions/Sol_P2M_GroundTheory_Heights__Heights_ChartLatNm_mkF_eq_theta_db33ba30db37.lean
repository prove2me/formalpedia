-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_mkF_eq_theta_db33ba30db37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:40.715943+00:00
-- url     : https://prove2.me/submissions/ab9c46bc-af28-4474-8bf8-94ac5e26b374

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
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g δ) :
    P.mkF g = theta P y hP hb (aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ))) *
      P.chartPow c (fun k => (δ k : ℤ)) := by
  have hM := isWeightedHomogeneous_chartMono c δ
  have hMy : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = ∏ k, y ⟨k, c k⟩ ^ δ k := by
    simp [map_prod]
  have hMy0 : aeval y (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0 := by
    rw [hMy]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hMF : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) = P.chartPow c (fun k => (δ k : ℤ)) := by
    simp [ArithVariety.chartPow, map_prod, zpow_natCast]
  have hne : P.mkF (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ^ δ k) ≠ 0 :=
    fun h => hMy0 ((mkF_eq_zero_iff' P y hP hM).mp h)
  rw [theta_eq P y hP hb hg hM hMy0, ← hMF, div_mul_cancel₀ _ hne]
  rw [hMy, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc k))]), mul_one]
end GroundTheory.Heights₂.Heights.ChartLatNm
