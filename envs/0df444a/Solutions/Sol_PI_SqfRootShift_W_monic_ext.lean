-- Prove2me | solution 1 for PI.SqfRootShift.W.monic_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:40.239584+00:00
-- url     : https://prove2.me/submissions/8a1d63c6-9b4d-40c3-9342-22bf0b99d16a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootShift.W
theorem _root_.solution {h1 h2 : (ZMod g)[X]} {m : ℕ} (hm1 : h1.Monic) (hm2 : h2.Monic)
    (hd1 : h1.natDegree = m) (hd2 : h2.natDegree = m)
    (hc : ∀ i < m, h1.coeff i = h2.coeff i) : h1 = h2 := by
  ext n
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact hc n hlt
  · have e1 : h1.coeff m = 1 := by rw [← hd1]; exact hm1.coeff_natDegree
    have e2 : h2.coeff m = 1 := by rw [← hd2]; exact hm2.coeff_natDegree
    rw [heq, e1, e2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
end PI.SqfRootShift.W
