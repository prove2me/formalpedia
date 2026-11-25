-- Prove2me | solution 1 for PI.UD.eq_zero_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:55.040947+00:00
-- url     : https://prove2.me/submissions/8b6a1eff-04cf-42b2-9c25-29358e253130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
import Theorems.Thm_PI_UD_circle_infinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution {σ : Type*} (R : MvPolynomial σ ℂ)
    (h : ∀ t : σ → ℂ, (∀ i, ‖t i‖ = 1) → eval t R = 0) : R = 0 :=
  MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => circle_infinite)
    fun t ht => by simpa using h t fun i => ht i (Set.mem_univ i)
end PI.UD
