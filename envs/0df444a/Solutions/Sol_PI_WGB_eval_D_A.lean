-- Prove2me | solution 1 for PI.WGB.eval_D_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:07.911508+00:00
-- url     : https://prove2.me/submissions/9cec46cb-e165-4346-8314-b3a49bbaba69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mono_eq_A

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) :
    eval x g = coeff (mStarA kap ν) g * ∏ v, x v ^ (mStarA kap ν) v := by
  rw [MvPolynomial.eval_eq']
  by_cases hs : mStarA kap ν ∈ g.support
  · rw [Finset.sum_eq_single (mStarA kap ν)]
    · intro m hm hne
      by_contra hz
      have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
      exact hne (mono_eq_A kap ν g hcol hrow x hx m hm hprod)
    · intro h
      exact absurd hs h
  · have hc : coeff (mStarA kap ν) g = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [hc, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hz
    have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact hs (mono_eq_A kap ν g hcol hrow x hx m hm hprod ▸ hm)
end PI.WGB
