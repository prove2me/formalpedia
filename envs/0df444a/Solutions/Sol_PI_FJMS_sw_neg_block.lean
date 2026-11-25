-- Prove2me | solution 1 for PI.FJMS.sw_neg_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:55.179731+00:00
-- url     : https://prove2.me/submissions/b2e06a76-cabe-49db-be84-d859f32a5c3a

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
    (hA : ∀ c, c ∉ Set.range j → e (w c) = 0) (hin : ∀ k, pos (j k) = false) :
    sw e w pos = -((∑ k, e (w (j k)) : ℕ) : ℤ) := by
  unfold sw
  rw [sum_range_emb j hj _ (fun c hc => by rw [hA c hc]; simp), Nat.cast_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [if_neg (by simp [hin k])])
end PI.FJMS
