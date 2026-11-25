-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:43.204753+00:00
-- url     : https://prove2.me/submissions/44ddd30d-c3f9-4582-9803-a4972eefc6c6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_cc_add
import Theorems.Thm_PI_FglPhSplit_Wk_cc_add
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst


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
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ τ : Type} [Finite σ] (r : σ → τ) {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    ren r (be l ex ph x y) = be l ex ph (ren r x) (ren r y) := by
  unfold be phAt
  rw [map_sub, map_sub, ren_psubst r _ (cc_add hex0 hl0 hx hy), ren_psubst r _ hx, ren_psubst r _ hy]
  congr 3
  unfold add pt lg
  rw [ren_psubst r _ (by rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx,
    PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero]), map_add, ren_psubst r _ hx, ren_psubst r _ hy]
end PI.UnitaryGroupMassFormula.PhDualGram
