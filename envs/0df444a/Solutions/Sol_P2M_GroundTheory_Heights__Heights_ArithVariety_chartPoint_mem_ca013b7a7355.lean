-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_chartPoint_mem_ca013b7a7355
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:29.247795+00:00
-- url     : https://prove2.me/submissions/e1f45b3e-68c8-43a8-ba1e-f2b067038a06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_evalCone_chartPoint_cf5b16f39004
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMap_eq_zero_8731551ff692

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
    (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ) :
    P.chartPoint c ψ ∈ P.points (AlgebraicClosure ℚ) := by
  refine ⟨fun k h ↦ ?_, fun f hf ↦ ?_⟩
  · have h1 : (P.chartMap c).rangeRestrict (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      change P.chartMap c (X ⟨k, c k⟩) = 1
      rw [chartMap, aeval_X, chartCoord]
      exact div_self fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    have h2 : P.chartPoint c ψ k (c k) = 1 := by
      rw [chartPoint, h1, map_one]
    rw [h] at h2
    exact zero_ne_one h2
  · rw [evalCone_chartPoint]
    have : (P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f) = 0 :=
      Subtype.ext (P.chartMap_eq_zero c hc hf)
    rw [this, map_zero]
end GroundTheory.Heights₂.Heights.ArithVariety
