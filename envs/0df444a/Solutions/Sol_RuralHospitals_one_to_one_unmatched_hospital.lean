-- Prove2me | solution 1 for RuralHospitals.one_to_one_unmatched_hospital
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T21:39:12.129198+00:00
-- url     : https://prove2.me/submissions/a57719a7-7632-493b-8117-451156471f58

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (h : H) (hh : assigned μ h = ∅) :
    assigned ν h = ∅ := by
  have h2 := (rural_hospitals_theorem M μ ν hμ hν).2.1 h
  rw [hh, Finset.card_empty] at h2
  exact Finset.card_eq_zero.mp h2.symm
