-- Prove2me | solution 1 for PI.LocLatEq.W.int_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:12.863481+00:00
-- url     : https://prove2.me/submissions/4e94597c-b244-4127-8311-2222b71166f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.LocLatEq.W
theorem _root_.solution (A : LocAt F E sig p) (x : F) (hx : A.ιF x ∈ 𝒪[A.Fp]) :
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * x = n := by
  rw [Valuation.mem_integer_iff] at hx
  have h1 : A.ιF x ≤ᵥ A.ιF 1 := by
    rw [map_one, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A.Fp), map_one]
    exact hx
  have hv : p.valuation F x ≤ 1 := by
    have := (A.val x 1).mp h1
    rwa [map_one] at this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p x hv
  refine ⟨d, d.2, n, ?_⟩
  rw [mul_comm]
  exact hnd
end PI.LocLatEq.W
