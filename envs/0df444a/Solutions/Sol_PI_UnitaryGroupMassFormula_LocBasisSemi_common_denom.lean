-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocBasisSemi.common_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:27.90038+00:00
-- url     : https://prove2.me/submissions/835d99be-188d-40a5-bde2-6bcf1ff8a445

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocBasisSemi_mem_T

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocBasisSemi
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}
namespace PI.UnitaryGroupMassFormula.LocBasisSemi
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ι → A K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : ι → 𝓞 K, ∀ i, (s : K) * (c i : K) = (x i : K) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (T K p) c
  choose x hx using hb
  obtain ⟨s, hs, u, hu⟩ := mem_T b.2
  refine ⟨s, hs, fun i => u * x i, fun i => ?_⟩
  have hK : ((x i : 𝓞 K) : K) = ((b : 𝓞 K) : K) * (c i : K) :=
    congrArg (fun y : A K p => (y : K)) (hx i)
  have hu' : (s : K) = (u : K) * ((b : 𝓞 K) : K) := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hu
    simpa using this
  rw [hu', show ((u * x i : 𝓞 K) : K) = (u : K) * (x i : K) from rfl, hK]
  ring
end PI.UnitaryGroupMassFormula.LocBasisSemi
