-- Prove2me | solution 1 for PI.OddDualWeyl.Misc.colSpan_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:58:38.746462+00:00
-- url     : https://prove2.me/submissions/47190f86-2a5a-406a-9bb2-23459a871ccf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_ExistsEqMulOfColumnSpanLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Misc
variable {O K : Type} [CommRing O] [Field K] [Algebra O K]
namespace PI.OddDualWeyl.Misc
theorem _root_.solution {n : ℕ} (h' : Matrix (Fin n) (Fin n) K) (v : Matrix (Fin n) (Fin n) O) :
    colSpan O (h' * v.map (algebraMap O K)) ≤ colSpan O h' := by
  unfold PI.OddDualWeyl.colSpan
  rw [Submodule.span_le]
  rintro x ⟨c, rfl⟩
  have hv : (fun i => (h' * v.map (algebraMap O K)) i c) = ∑ j, v j c • fun i => h' i j := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, Matrix.mul_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  dsimp only
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end PI.OddDualWeyl.Misc
