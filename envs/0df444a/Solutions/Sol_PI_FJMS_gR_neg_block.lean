-- Prove2me | solution 1 for PI.FJMS.gR_neg_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:44.720063+00:00
-- url     : https://prove2.me/submissions/8eadd644-caeb-40b4-8da1-64c513083827

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_gR_pos_block
import Theorems.Thm_PI_FJMP_gR_swap


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
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {σ κ : Type*} [Fintype κ]
namespace PI.FJMS
theorem _root_.solution {m : ℕ} (u v : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (P : MvPolynomial σ ℂ) (hA : ∀ c, c ∉ Set.range j → NoVar P (u c))
    (hB : ∀ c, c ∉ Set.range j → NoVar P (v c)) (hin : ∀ k, pos (j k) = false) :
    gR u v pos P = -∑ k, X (v (j k)) * pderiv (u (j k)) P := by
  have h := gR_swap u v pos P
  rw [gR_pos_block v u (fun c => !pos c) j hj P hB hA (fun k => by simp [hin k])] at h
  rw [h, neg_neg]
end PI.FJMS
