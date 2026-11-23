-- Prove2me | solution 1 for PI.WGB.fockF_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:12.381737+00:00
-- url     : https://prove2.me/submissions/6a616b1a-c449-43be-a77c-dcf74dcdafe7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Theorems.Thm_PI_WGB_fockF_eq_sum

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
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {σ : Type} (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fockF (c • p) q = c * fockF p q := by
  classical
  rw [fockF_eq_sum (c • p) q p.support (fun m h _ => by
        rw [MvPolynomial.coeff_smul, smul_eq_mul] at h
        exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)),
    fockF_eq_sum p q p.support (fun m h _ => MvPolynomial.mem_support_iff.mpr h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring
end PI.WGB
