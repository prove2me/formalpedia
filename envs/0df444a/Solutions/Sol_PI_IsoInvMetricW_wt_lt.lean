-- Prove2me | solution 1 for PI.IsoInvMetricW.wt_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:19.772262+00:00
-- url     : https://prove2.me/submissions/c0d19b7e-cab5-4e61-b40c-5bfc77b4f42d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
import Theorems.Thm_PI_IsoInvMetricW_emb_ge
import Theorems.Thm_PI_IsoInvMetricW_column_index_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) (hJ : J ≠ J0 nu hle) :
    wt J < wt (J0 nu hle) := by
  have hex : ∃ s c i, J s c i ≠ J0 nu hle s c i := by
    by_contra hc
    push Not at hc
    apply hJ
    funext s c
    exact DFunLike.ext _ _ (hc s c)
  obtain ⟨s0, c0, i0, h0⟩ := hex
  have hv : ((J s0 c0 i0 : Fin N) : ℕ) ≠ i0 := by
    intro e; apply h0; apply Fin.ext; rw [e, column_index_val]
  have hterm : ∀ s c i, N - ((J s c i : Fin N) : ℕ) ≤ N - ((J0 nu hle s c i : Fin N) : ℕ) := by
    intro s c i; rw [column_index_val]; have := emb_ge (J s c) i; omega
  unfold wt
  apply Finset.sum_lt_sum (fun s _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => hterm s c i)
  refine ⟨s0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun c _ => Finset.sum_le_sum fun i _ => hterm s0 c i)
  refine ⟨c0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun i _ => hterm s0 c0 i)
  refine ⟨i0, Finset.mem_univ _, ?_⟩
  rw [column_index_val]
  have := emb_ge (J s0 c0) i0
  have := (J s0 c0 i0).isLt
  omega
end PI.IsoInvMetricW
