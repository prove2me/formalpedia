-- Prove2me | solution 1 for PI.OddDualWeyl.highest_weight_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:29.945245+00:00
-- url     : https://prove2.me/submissions/65bf09a5-179a-466f-9902-4bf65321e072

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_rowGen
import Theorems.Thm_PI_OddDualWeyl_Hom_toZ
import Theorems.Thm_PI_OddDualWeyl_Hom_ofZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Hom
namespace PI.OddDualWeyl
theorem _root_.solution : MHdiv := by
  intro R _ k a b j f hf c
  obtain ⟨d, hd⟩ := hf c
  refine ⟨_, ofZ (good_rowGen (wt := fun v => ((rowW c v : ℕ) : ℤ))
    (δ := ((if a = c then 1 else 0 : ℕ) : ℤ) - ((if b = c then 1 else 0 : ℕ) : ℤ)) a b ?_ (toZ hd) j)⟩
  intro s
  simp only [rowW]
  split_ifs <;> simp
end PI.OddDualWeyl
