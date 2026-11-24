-- Prove2me | solution 1 for PI.FockOneDegW.HwC.posC_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:42.774533+00:00
-- url     : https://prove2.me/submissions/f2232f95-aa33-40a4-af1e-f1d0622e4ef2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists

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
open PI PI.FockOneDegW PI.FockOneDegW.HwC
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q : ℕ} {a b : Ix p q} (h : posC a b) :
    sameBlock a b ∧ a ≠ b ∧ tw b < tw a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inl.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inr.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')
end PI.FockOneDegW.HwC
