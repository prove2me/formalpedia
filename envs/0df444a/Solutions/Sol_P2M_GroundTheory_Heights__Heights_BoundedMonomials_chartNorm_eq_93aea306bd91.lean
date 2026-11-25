-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_eq_93aea306bd91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:33.396032+00:00
-- url     : https://prove2.me/submissions/723b4fc5-f743-4a4a-adb0-ff4e522adf80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial_ne_zero_cbad317c02fd

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
open GroundTheory.Heights₂.Heights.BoundedMonomials
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg) {z : Cone n ℂ}
    (hz : z ∈ P.points ℂ) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} {e e' : MvPolynomial (Coord n) ℤ}
    (he : IsChartForm P A.deg s.num s.den c d e) (he' : IsChartForm P A.deg s.num s.den c' d' e')
    (hc : ∀ k, z k (c k) ≠ 0) (hc' : ∀ k, z k (c' k) ≠ 0) :
    chartNorm A c d e z = chartNorm A c' d' e' z := by
  set m := chartMonomial c d
  set m' := chartMonomial c' d'
  have hmem : e * m' - e' * m ∈ P.ideal := by
    have h : s.den * (e * m' - e' * m) =
        (s.den * e - s.num * m) * m' - (s.den * e' - s.num * m') * m := by ring
    have h2 : s.den * (e * m' - e' * m) ∈ P.ideal := by
      rw [h]
      exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
    exact (P.isPrime.mem_or_mem h2).resolve_left s.den_not_mem
  have h0 : evalCone z (e * m' - e' * m) = 0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0
  have hn : ‖evalCone z e‖ * ‖evalCone z m'‖ = ‖evalCone z e'‖ * ‖evalCone z m‖ := by
    rw [← norm_mul, ← norm_mul]
    exact congrArg norm h0
  have hh : 0 < A.metric z := A.metric_pos z hz.1
  have hm : ‖evalCone z m‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d hc)
  have hm' : ‖evalCone z m'‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d' hc')
  unfold chartNorm
  rw [div_eq_div_iff (mul_ne_zero hm hh.ne') (mul_ne_zero hm' hh.ne')]
  calc ‖evalCone z e‖ * (‖evalCone z m'‖ * A.metric z)
      = (‖evalCone z e‖ * ‖evalCone z m'‖) * A.metric z := by ring
    _ = (‖evalCone z e'‖ * ‖evalCone z m‖) * A.metric z := by rw [hn]
    _ = ‖evalCone z e'‖ * (‖evalCone z m‖ * A.metric z) := by ring
end GroundTheory.Heights₂.Heights.BoundedMonomials
