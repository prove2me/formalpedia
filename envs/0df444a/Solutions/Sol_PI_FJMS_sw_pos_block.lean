-- Prove2me | solution 1 for PI.FJMS.sw_pos_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:57.254562+00:00
-- url     : https://prove2.me/submissions/59f33a53-1d66-4b65-8b43-d4f2be65762e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Theorems.Thm_PI_FJMS_sum_range_emb

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
theorem _root_.solution {m : ℕ} (e : σ →₀ ℕ) (w : κ → σ) (pos : κ → Bool) (j : Fin m → κ) (hj : Function.Injective j)
    (hA : ∀ c, c ∉ Set.range j → e (w c) = 0) (hin : ∀ k, pos (j k) = true) :
    sw e w pos = ((∑ k, e (w (j k)) : ℕ) : ℤ) := by
  unfold sw
  rw [sum_range_emb j hj _ (fun c hc => by rw [hA c hc]; simp), Nat.cast_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [if_pos (hin k)])
end PI.FJMS
