-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScalDeg.prod_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:55.427682+00:00
-- url     : https://prove2.me/submissions/c9b32856-b440-4be0-acc4-a204257f7ce9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
open Classical
namespace PI.UnitaryGroupMassFormula.ScalDeg
theorem _root_.solution {T : Type} [Fintype T] {N : ℕ} (s : T → ℂ) (v : FrV T N →₀ ℕ) :
    (v.prod fun k n => s k.1 ^ n) =
      ∏ τ, s τ ^ (v.sum fun k n => if k.1 = τ then n else 0) := by
  unfold Finsupp.prod Finsupp.sum
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq]
  simp
end PI.UnitaryGroupMassFormula.ScalDeg
