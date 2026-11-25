-- Prove2me | solution 1 for PI.SqPairLocal.divAt_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:59.737464+00:00
-- url     : https://prove2.me/submissions/5ad1d49a-8291-40e3-b49e-daa6415dcb15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_mul_nmem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime]
namespace PI.SqPairLocal
theorem _root_.solution {c d : 𝓞 E} {K : ℕ}
    (hK : ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w) (hd : d ∈ Q ^ K) {x : E}
    (hx : DivAt Q d x) : DivAt Q c x := by
  unfold DivAt at *
  obtain ⟨s, hs, w, hw⟩ := hK d hd
  have hsd : (s : E) * (d : E) = (c : E) * (w : E) := by
    exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hw
  obtain ⟨t, ht, v, hv⟩ := hx
  refine ⟨s * t, mul_nmem hs ht, w * v, ?_⟩
  push_cast
  linear_combination (s : E) * hv + (v : E) * hsd
end PI.SqPairLocal
