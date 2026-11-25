-- Prove2me | solution 1 for PI.GreenLabelMapW.gen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:21.569705+00:00
-- url     : https://prove2.me/submissions/3dec7a64-ecb3-4615-bba7-45e304431d9f

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Theorems.Thm_PI_GreenLabelMapW_gen_pow
import Theorems.Thm_PI_GreenLabelMapW_card_pow_sub_one_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (Cv : LabelConv K) {d : ℕ} (hd : 1 ≤ d) : Cv.gen d ≠ 0 := by
  intro h
  have h1 := gen_pow Cv hd
  have h2 := card_pow_sub_one_pos (K := K) hd
  rw [h, zero_pow (by omega)] at h1
  exact zero_ne_one h1
end PI.GreenLabelMapW
