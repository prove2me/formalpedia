-- Prove2me | solution 1 for RuralHospitals.rural_hospitals_part2
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T21:33:56.852983+00:00
-- url     : https://prove2.me/submissions/43b8a1d1-f2ce-4e83-b87f-76c5a40b5547

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Theorems.Thm_RuralHospitals_rural_hospitals_theorem

set_option autoImplicit false

open RuralHospitals Finset

theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν)
    (h : H) (hh : (assigned μ h).card < M.capacity h) :
    assigned ν h = assigned μ h :=
  (rural_hospitals_theorem M μ ν hμ hν).2.2 h hh
