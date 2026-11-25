-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramUnit.inv_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:01.66401+00:00
-- url     : https://prove2.me/submissions/924d2370-de26-4e2d-8dbf-99c6f4c464ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramUnit
namespace PI.UnitaryGroupMassFormula.GramUnit
theorem _root_.solution {K : Type*} [Field K] (l ex : PowerSeries K) (h0 : constantCoeff ex = 0)
    (hle : subst ex l = X) : subst l ex = X ∧ constantCoeff l = 0 := by
  have hex : HasSubst ex := HasSubst.of_constantCoeff_zero' h0
  obtain ⟨u, hu⟩ : (X : PowerSeries K) ∣ ex := X_dvd_iff.mpr h0
  have hc : constantCoeff l = 0 := by
    have h1 := congrArg (coeff 0) hle
    rw [coeff_subst' hex, finsum_eq_single _ 0] at h1
    · rw [← coeff_zero_eq_constantCoeff_apply]
      simpa using h1
    · intro d hd
      rw [hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  have h1 : coeff 1 l * coeff 1 ex = 1 := by
    have h1 := congrArg (coeff 1) hle
    rw [coeff_subst' hex, finsum_eq_single _ 1] at h1
    · simpa using h1
    · intro d hd
      rcases d with _ | _ | d
      · simp
      · exact absurd rfl hd
      · rw [hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  have hunit : IsUnit (coeff 1 ex) := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
  obtain ⟨q, hq, hr⟩ : ∃ q : PowerSeries K, HasSubst q ∧ subst q ex = X :=
    ⟨_, HasSubst.substInvOfIsUnit ex hunit, subst_substInvOfIsUnit_right ex h0 hunit⟩
  have e1 : subst q (subst ex l) = subst (subst q ex) l := subst_comp_subst_apply hex hq l
  rw [hr, hle, X_subst, subst_X hq] at e1
  refine ⟨?_, hc⟩
  rw [← e1]
  exact hr
end PI.UnitaryGroupMassFormula.GramUnit
