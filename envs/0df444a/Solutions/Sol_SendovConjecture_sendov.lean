-- Prove2me | solution 1 for SendovConjecture.sendov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:42:57.943029+00:00
-- url     : https://prove2.me/submissions/c07b888f-7676-4ded-b17b-ae59f69f7fa3

import Definitions.Def_Sendov_Conjecture
import Definitions.Def_Sendov_Solution
import Theorems.Thm_Sendov_sendov


set_option autoImplicit false
open SendovConjecture
open Polynomial
namespace SendovConjecture
theorem _root_.solution {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 :=
  Sendov.sendov (n := p.natDegree) hdeg rfl (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa
end SendovConjecture
