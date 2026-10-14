-- Prove2me | solution 1 for RuralHospitals.rural_hospitals_part1
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T21:30:58.136721+00:00
-- url     : https://prove2.me/submissions/7d943218-0bcd-4f07-9f87-af736c91b315

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, (μ d).isSome = (ν d).isSome) ∧
      ∀ h, (assigned μ h).card = (assigned ν h).card :=
  ⟨(rural_hospitals_theorem M μ ν hμ hν).1, (rural_hospitals_theorem M μ ν hμ hν).2.1⟩
