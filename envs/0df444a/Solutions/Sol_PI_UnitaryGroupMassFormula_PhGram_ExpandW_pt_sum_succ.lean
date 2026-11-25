-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.pt_sum_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:38.758485+00:00
-- url     : https://prove2.me/submissions/cc3d9e53-42cb-495c-9983-a91c19c6c4b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_add_pt
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_cc_sum_lg

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}
namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW
theorem _root_.solution (hd : Data l ex ph) {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p])
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    pt ex (∑ j, lg l (a j)) =
      add l ex (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc, ← add_pt hd (cc_sum_lg hd (fun j => ha (Fin.castSucc j)))]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
