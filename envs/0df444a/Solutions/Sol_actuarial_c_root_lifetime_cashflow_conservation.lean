-- Prove2me | solution 1 for actuarial_c_root_lifetime_cashflow_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:03:42.099264+00:00
-- url     : https://prove2.me/submissions/7e71dd9b-e74f-488a-a85b-1d0ac3791804

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_massPV
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_deferred
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_pureMass
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_secondMass
import Definitions.Def_actuarial_c_delayEPV
import Definitions.Def_actuarial_c_weightedDue
import Definitions.Def_actuarial_c_increasingDue
import Definitions.Def_actuarial_c_differenceBenefit
import Definitions.Def_actuarial_c_termSecond
import Definitions.Def_actuarial_c_endowSecond
import Definitions.Def_actuarial_c_expectedLoss
import Definitions.Def_actuarial_c_netPremium
import Definitions.Def_actuarial_c_massCohort
import Definitions.Def_actuarial_faM
import Theorems.Thm_actuarial_c_deferred_split
import Theorems.Thm_actuarial_c_delay_epv_factor
import Theorems.Thm_actuarial_c_endow_add
import Theorems.Thm_actuarial_c_endowment_second_decomposition
import Theorems.Thm_actuarial_c_epv_equals_mass
import Theorems.Thm_actuarial_c_finite_assurance_annuity
import Theorems.Thm_actuarial_c_general_insurance_annuity
import Theorems.Thm_actuarial_c_increasing_insurance_annuity
import Theorems.Thm_actuarial_c_mass_to_public_commutation_M
import Theorems.Thm_actuarial_c_net_premium_zero_expected_loss
import Theorems.Thm_actuarial_c_pure_reconcile
import Theorems.Thm_actuarial_c_second_reconcile

open ActuarialAssurances
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
theorem solution(h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hm : total h p=1) (hn : n ≤ h) (hv : 0 < v) (hv1 : v ≤ 1) : (epv h v b p=massPV h v b p) ∧ (pure h n v p=pureMass h n v p) ∧ (endow h n v b p=term h n v b p+pure h n v p) ∧ (term h n v (fun _ => 1) p+pureMass h n v p+(1-v)*due h n v p=1) ∧ (second h v b p=secondMass h v b p) ∧ (endowSecond h n v b p=termSecond h n v b p+v^(2*n)*surv h p n) ∧ (epv h v b p+(1-v)*weightedDue h v b p+v^h*b (h-1)*surv h p h=differenceBenefit h v b p) ∧ (massPV h v (fun _ => 1) p=ActuarialFoundations.faM (massCohort h p) v h 0) ∧
(term h h v b p=term h n v b p+deferred h n (h-n) v b p) ∧
(delayEPV h 1 v b p=v*epv h v b p) ∧
(epv h v inc p+(1-v)*increasingDue h v p+(h : ℝ)*v^h*surv h p h=due h h v p) ∧
(0 < due h n v p → expectedLoss h n v (netPremium h n v b p) b p=0) := by
  refine ⟨actuarial_c_epv_equals_mass h v b p,
    actuarial_c_pure_reconcile h n v p,
    actuarial_c_endow_add h n v b p,
    actuarial_c_finite_assurance_annuity h n v p hn hm,
    actuarial_c_second_reconcile h v b p,
    actuarial_c_endowment_second_decomposition h n v b p hn,
    actuarial_c_general_insurance_annuity h v b p,
    actuarial_c_mass_to_public_commutation_M h v p,
    ?_, ?_, actuarial_c_increasing_insurance_annuity h v p, ?_⟩
  · have hs : n + (h-n) = h := Nat.add_sub_of_le hn
    simpa only [hs] using
      (actuarial_c_deferred_split h n (h-n) v b p (le_of_eq hs))
  · simpa using (actuarial_c_delay_epv_factor h 1 v b p)
  · intro ha
    exact actuarial_c_net_premium_zero_expected_loss h n v b p ha
