-- Prove2me | solution 1 for PI.StabSplit.Proj.exists_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:22.215906+00:00
-- url     : https://prove2.me/submissions/cb54ad36-a71e-4b0f-aaf0-f819425bd488

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabSplit PI.StabSplit.Proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)
namespace PI.StabSplit.Proj
theorem _root_.solution (A : Matrix n ι ℂ)
    (hA : ∀ j, (fun i => A i j) ∈ Submodule.span ℂ (Set.range fun l => fun i => Y i l)) :
    ∃ C : Matrix ι ι ℂ, A = Y * C := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hA j)
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have h := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [mul_apply, ← h]
  simp [mul_comm]
end PI.StabSplit.Proj
