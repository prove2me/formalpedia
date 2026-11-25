-- Prove2me | solution 1 for PI.FockOneDegW.Core.coeff_zero_of_dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:04.109784+00:00
-- url     : https://prove2.me/submissions/5034b898-4167-4b07-af1e-aab281580ddb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Core
theorem _root_.solution {σ : Type*} (v : MvPolynomial σ ℂ) (i j : σ) (hij : i ≠ j)
    (h : pderiv i (pderiv j v) = 0) (α : σ →₀ ℕ) (hα : coeff α v ≠ 0) :
    α i = 0 ∨ α j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hi, hj⟩ := hcon
  have hsplit : α = (α - Finsupp.single i 1 - Finsupp.single j 1) + Finsupp.single i 1 +
      Finsupp.single j 1 := by
    ext k
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2 <;> (try subst_vars) <;> first | omega | exact (hij rfl).elim
  obtain ⟨m, hm⟩ : ∃ m, α = m + Finsupp.single i 1 + Finsupp.single j 1 := ⟨_, hsplit⟩
  have hc := congrArg (coeff m) h
  rw [coeff_pderiv, coeff_pderiv, coeff_zero, ← hm] at hc
  rcases mul_eq_zero.1 hc with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact hα h''
    · exact Nat.cast_add_one_ne_zero _ h''
  · exact Nat.cast_add_one_ne_zero _ h'
end PI.FockOneDegW.Core
