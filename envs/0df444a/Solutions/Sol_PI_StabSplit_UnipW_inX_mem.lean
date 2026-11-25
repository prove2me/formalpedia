-- Prove2me | solution 1 for PI.StabSplit.UnipW.inX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:46:16.401235+00:00
-- url     : https://prove2.me/submissions/6c51e554-ecc3-42cf-8fd0-31fcb9c257ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {k r : ℕ} {x : Fin (2 * r + k + 1) → ℂ} (hx : inX k r x) : x ∈ Xsp k r := by
  have hx' : x = ∑ a : Fin r, x (eI k r a) • bvec (eI k r a) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
      · have e : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
        rw [if_pos e, ← e]
      · intro a _ ha
        rw [if_neg]
        intro h
        apply ha
        ext
        have := congrArg Fin.val h
        simp only [eI] at this
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hx i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro h
      apply hi
      rw [h]
      exact a.2
  rw [hx']
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
end PI.StabSplit.UnipW
