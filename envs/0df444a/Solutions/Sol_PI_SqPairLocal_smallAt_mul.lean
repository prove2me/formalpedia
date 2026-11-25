-- Prove2me | solution 1 for PI.SqPairLocal.smallAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:03.982416+00:00
-- url     : https://prove2.me/submissions/b991dc32-fc36-4295-86b5-b00be1a4d6da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

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
variable {N : ℕ}
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution {M B : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M) (hB : Pres L B) :
    SmallAt Q c L (M * B) := by
  intro y hy
  obtain ⟨s, hs, m, hm, h1⟩ := h _ (hB y hy)
  exact ⟨s, hs, m, hm, by rw [← Matrix.mulVec_mulVec, h1]⟩
end PI.SqPairLocal
