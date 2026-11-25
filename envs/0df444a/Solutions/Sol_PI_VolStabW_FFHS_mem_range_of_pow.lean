-- Prove2me | solution 1 for PI.VolStabW.FFHS.mem_range_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:14.621297+00:00
-- url     : https://prove2.me/submissions/ee4206bf-e278-4230-8e9b-cd68f7adc014

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module Polynomial
variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]
namespace PI.VolStabW.FFHS
theorem _root_.solution (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  by_contra H
  push_neg at H
  have hdm : d ∉ Finset.univ.image (algebraMap k K) := by simpa using H
  have := card_le_degree_of_subset_roots (p := (X ^ Fintype.card k - X : K[X]))
    (Z := insert d (Finset.univ.image (algebraMap k K))) (fun x hx => by
      rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot, eval_sub, eval_pow,
        eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hd
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
        rw [← map_pow, FiniteField.pow_card])
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_insert_of_notMem hdm,
    Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ] at this
  omega
end PI.VolStabW.FFHS
