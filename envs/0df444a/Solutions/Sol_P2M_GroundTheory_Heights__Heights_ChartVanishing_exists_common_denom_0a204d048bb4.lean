-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_common_denom_0a204d048bb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:11.838415+00:00
-- url     : https://prove2.me/submissions/b0db5dc6-995c-48f2-b619-0c1a1499a971

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_clear_denom_4864fe822f9f

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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by
  choose e f hf using fun j ↦ exists_clear_denom P hc (hu j)
  refine ⟨∑ j, e j, fun j ↦ f j * chartMonomial c 1 ^ (∑ i, e i - e j), fun j ↦ ?_⟩
  have hle : e j ≤ ∑ i, e i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (e i)) (Finset.mem_univ j)
  rw [map_mul, map_pow, ← hf j, ← Nat.add_sub_cancel' hle, pow_add, Nat.add_sub_cancel_left]
  ring
end GroundTheory.Heights₂.Heights.ChartVanishing
