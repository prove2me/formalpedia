-- Prove2me | solution 1 for PI.FJMP.noVar_of_pderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:42.55981+00:00
-- url     : https://prove2.me/submissions/cf811b98-bf5b-4fc1-8e7f-85eab18a5a69

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

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
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
namespace PI.FJMP
theorem _root_.solution {P : MvPolynomial σ ℂ} {v : σ} (h : pderiv v P = 0) : NoVar P v := by
  classical
  intro e he
  by_contra hev
  have hc : coeff (e - Finsupp.single v 1) (pderiv v P) = coeff e P * (e v : ℂ) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, coeff_sum]
    simp only [pderiv_monomial, coeff_monomial]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro b _ hbe
      by_cases hbv : b v = 0
      · simp [hbv]
      · rw [if_neg]
        intro hb
        apply hbe
        have h1 : Finsupp.single v 1 ≤ b := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hbv)
        have h2 : Finsupp.single v 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hev)
        rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, hb]
    · intro h'
      exact absurd he h'
  rw [h, coeff_zero] at hc
  exact mul_ne_zero (mem_support_iff.mp he) (Nat.cast_ne_zero.mpr hev) hc.symm
end PI.FJMP
