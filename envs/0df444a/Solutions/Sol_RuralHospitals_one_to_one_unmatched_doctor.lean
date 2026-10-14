-- Prove2me | solution 1 for RuralHospitals.one_to_one_unmatched_doctor
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T21:36:18.616581+00:00
-- url     : https://prove2.me/submissions/52f91130-1113-4b81-923e-b22ba1510c37

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (hcap : ∀ h, M.capacity h = 1) (μ ν : Assignment D H)
    (hμ : M.IsStable μ) (hν : M.IsStable ν) (d : D) (hd : μ d = none) :
    ν d = none := by
  have h1 := (rural_hospitals_theorem M μ ν hμ hν).1 d
  rw [hd, Option.isSome_none] at h1
  exact Option.not_isSome_iff_eq_none.mp (by simp [← h1])
