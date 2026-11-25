-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:36.062342+00:00
-- url     : https://prove2.me/submissions/dd4d123e-61f0-4a5f-93f0-f7ae3469e7ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_map_94d14512901d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chart_homogeneous_b02eed3f7c1c

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
variable (P : ArithVariety n)
variable (c : (k : ι) → Fin (n k + 1))
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = 0 := by
  classical
  rw [chartMap_map]
  have hcomp : ∀ m : ι → ℕ,
      eval₂ (Int.castRingHom _) (P.chartCoord c) (weightedHomogeneousComponent (coordDeg n) m f) = 0 := by
    intro m
    have h := P.chart_homogeneous c hc (weightedHomogeneousComponent_isWeightedHomogeneous m f)
    rw [(P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m)] at h
    have hne : (∏ k, P.mkF (X ⟨k, c k⟩) ^ m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    exact (mul_eq_zero.mp h).resolve_left hne
  conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), eval₂_sum]
  exact Finset.sum_eq_zero fun m _ ↦ hcomp m
end GroundTheory.Heights₂.Heights.ArithVariety
