-- Prove2me | solution 1 for PI.SqPairLocal.smallAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:59.515534+00:00
-- url     : https://prove2.me/submissions/031e7ab2-6b10-4ebd-9e05-337b6cbe5264

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
theorem _root_.solution {M M' : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M)
    (h' : SmallAt Q c L M') : SmallAt Q c L (M + M') := by
  intro y hy
  obtain ⟨s, hs, m, hm, h1⟩ := h y hy
  obtain ⟨s', hs', m', hm', h2⟩ := h' y hy
  refine ⟨s * s', fun hss => (hQ.mem_or_mem hss).elim hs hs', s' • m + s • m',
    L.add_mem (L.smul_mem _ hm) (L.smul_mem _ hm'), ?_⟩
  have e1 : (s * s') • (M *ᵥ y) = s' • (c • m) := by rw [mul_comm, mul_smul, h1]
  have e2 : (s * s') • (M' *ᵥ y) = s • (c • m') := by rw [mul_smul, h2]
  rw [Matrix.add_mulVec, smul_add, e1, e2]
  module
end PI.SqPairLocal
