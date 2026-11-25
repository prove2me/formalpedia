-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.mem_O_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:13.437526+00:00
-- url     : https://prove2.me/submissions/d2443ab6-0b08-42a4-a22d-8de41ac6d7bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution (I : Submodule (𝓞 E) E) (hI : I ≠ ⊥) (hfg : I.FG) (x : E)
    (hx : ∀ c ∈ I, x * c ∈ I) : InO x := by
  have hint : IsIntegral (𝓞 E) x :=
    isIntegral_of_smul_mem_submodule I hI hfg x (fun c hc => by simpa [smul_eq_mul] using hx c hc)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy⟩
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
