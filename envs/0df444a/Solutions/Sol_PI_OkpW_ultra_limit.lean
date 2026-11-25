-- Prove2me | solution 1 for PI.OkpW.ultra_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:56.132026+00:00
-- url     : https://prove2.me/submissions/69626351-5129-43a7-be87-215bae2db86f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub
import Theorems.Thm_PI_OkpW_ultra_tail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
namespace PI.OkpW
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]
    (x : ℕ → E) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, ‖x (k + 1) - x k‖ ≤ r ^ (k + 1)) :
    Tendsto x atTop (𝓝 (limUnder atTop x)) ∧ ∀ k, ‖limUnder atTop x - x k‖ ≤ r ^ (k + 1) := by
  have hc : CauchySeq x := cauchySeq_of_le_geometric r r hr1 (fun n => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h n)
  have ht := hc.tendsto_limUnder
  refine ⟨ht, fun k => ?_⟩
  have ht' : Tendsto (fun j => ‖x (j + k) - x k‖) atTop (𝓝 ‖limUnder atTop x - x k‖) :=
    (((tendsto_add_atTop_iff_nat k).mpr ht).sub_const (x k)).norm
  exact le_of_tendsto' ht' (fun j => ultra_tail x hr0 hr1.le h k j)
end PI.OkpW
