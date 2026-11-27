-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_ne_zero_6cdc192a5aea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:24.909005+00:00
-- url     : https://prove2.me/submissions/4190964a-5f8e-43e4-8a96-006755398a92

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
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ)
    (hfP : f ∉ P.ideal) : (P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f) ≠ 0 := by
  intro h
  have h0 : P.chartMap c (map (Int.castRingHom ℚ) f) = 0 := congrArg Subtype.val h
  rw [chartMap_map] at h0
  have h1 := P.chart_homogeneous c hc hf
  rw [h0, mul_zero, eq_comm, P.mkF_eq_zero_iff] at h1
  exact hfP h1
end GroundTheory.Heights₂.Heights.ArithVariety
