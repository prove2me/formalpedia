-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isOfDegree_mul_93013abb2ad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:40.340829+00:00
-- url     : https://prove2.me/submissions/673668ab-4066-496b-aefc-5a66780a0e2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis

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
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (P : ArithVariety n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {a b : ι → ℤ} {x y : P.FunField} (hx : P.IsOfDegree a x) (hy : P.IsOfDegree b y) :
    P.IsOfDegree (a + b) (x * y) := by
  obtain ⟨f, g, δf, δg, hf, hg, hδ, hgP, rfl⟩ := hx
  obtain ⟨f', g', δf', δg', hf', hg', hδ', hgP', rfl⟩ := hy
  refine ⟨f * f', g * g', δf + δf', δg + δg', hf.mul hf', hg.mul hg', fun k ↦ ?_,
    fun h ↦ (P.isPrime.mem_or_mem h).elim hgP hgP', ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    linear_combination hδ k + hδ' k
  · rw [map_mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.MonomialMapNorm
