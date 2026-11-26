-- Prove2me | solution 1 for Sendov.sendov_boundary_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:48.942006+00:00
-- url     : https://prove2.me/submissions/493e97b8-787b-4dbf-94e7-e78394a448ec

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_rubinstein_one
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 := by
  rcases rubinstein_one hn hdeg hroots hp1 with ⟨ζ, hζ, hlt⟩ | hext
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  refine ⟨0, ?_, by norm_num⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_one]
  simp [zero_pow (by omega : n - 1 ≠ 0)]
end Sendov
