-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:50.302277+00:00
-- url     : https://prove2.me/submissions/7eb3f7ec-5bd2-4263-b321-157ce6575f99

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_C
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_lin

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
include hl0
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    ren r (lin l ex c w) = lin l ex c (fun j => ren r (w j)) := by
  unfold lin pt
  rw [ren_psubst r _ (cc_lin hl0 c w hw), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ren_C, lg, lg, ren_psubst r _ (hw j)]
end PI.UnitaryGroupMassFormula.PhDualGram
