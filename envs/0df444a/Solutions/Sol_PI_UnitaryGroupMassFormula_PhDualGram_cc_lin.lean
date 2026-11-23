-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.cc_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:23.806465+00:00
-- url     : https://prove2.me/submissions/014d6d95-8550-4777-8de3-3cf426e3da41

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)
omit [Finite σ]
include hl0
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    constantCoeff (∑ j, C (c j) * lg l (w j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [map_mul, lg, PI.FglPhSplit.Wk.cc_psubst _ hl0 (hw j), mul_zero]
end PI.UnitaryGroupMassFormula.PhDualGram
