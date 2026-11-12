-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P77.additive_classical_failure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:23:36.818726+00:00
-- url     : https://prove2.me/submissions/ba5ee24d-59b2-45f1-af09-1089ab74a366

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {Omega : Type} [Fintype Omega]
    (p : Law Omega) (badIdeal badActual failed : Omega → Prop)
    (hagrees : ∀ w, ¬ failed w → (badActual w ↔ badIdeal w))
    (luck failure : ℝ)
    (hluck : (∑ w, if badIdeal w then p.prob w else 0) ≤ luck)
    (hfailure : (∑ w, if failed w then p.prob w else 0) ≤ failure) :
    (∑ w, if badActual w then p.prob w else 0) ≤ luck + failure := by
  have key : (∑ w, if badActual w then p.prob w else 0) ≤
      ∑ w, ((if badIdeal w then p.prob w else 0) + (if failed w then p.prob w else 0)) := by
    apply Finset.sum_le_sum
    intro w _
    have hp := p.nonneg w
    have hw := hagrees w
    split_ifs <;> first | linarith | (exfalso; tauto)
  rw [Finset.sum_add_distrib] at key
  linarith
