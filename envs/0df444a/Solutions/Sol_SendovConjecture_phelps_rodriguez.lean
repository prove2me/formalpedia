-- Prove2me | solution 1 for SendovConjecture.phelps_rodriguez
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:41:27.934845+00:00
-- url     : https://prove2.me/submissions/0fc43d18-c665-47f9-ac77-748ee897f9d9

import Definitions.Def_Sendov_Conjecture
import Definitions.Def_Sendov_Solution
import Theorems.Thm_Sendov_phelps_rodriguez


set_option autoImplicit false
open SendovConjecture
open Polynomial
namespace SendovConjecture
theorem _root_.solution {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
          p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) :=
  Sendov.phelps_rodriguez (n := p.natDegree) hdeg rfl
    (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa
end SendovConjecture
