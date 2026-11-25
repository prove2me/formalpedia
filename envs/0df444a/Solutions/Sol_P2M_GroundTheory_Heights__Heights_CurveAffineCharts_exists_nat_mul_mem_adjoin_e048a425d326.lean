-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_nat_mul_mem_adjoin_e048a425d326
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:32.86254+00:00
-- url     : https://prove2.me/submissions/868b9e13-e448-418c-81e9-8a8fde9cf60a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [CharZero K'] {S : Set K'} {x : K'} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ?_⟩
    have hq : (q.den : K') * algebraMap ℚ K' q = (q.num : K') := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [hq]
    exact intCast_mem _ _
  | add x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x + z) = (m : K') * ((n : K') * x) + (n : K') * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ m) hnx) (mul_mem (natCast_mem _ n) hmz)
  | mul x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x * z) = ((n : K') * x) * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem hnx hmz
end GroundTheory.Heights₂.Heights.CurveAffineCharts
