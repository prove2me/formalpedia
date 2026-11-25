-- Prove2me | solution 1 for PI.SqPairLocal.three_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:32.338089+00:00
-- url     : https://prove2.me/submissions/b3f53771-27f3-43e9-ac64-e1c789f0781e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Theorems.Thm_PI_SqPairLocal_pres_one_sub
import Theorems.Thm_PI_SqPairLocal_smallAt_add
import Theorems.Thm_PI_SqPairLocal_smallAt_neg
import Theorems.Thm_PI_SqPairLocal_smallAt_mul
import Theorems.Thm_PI_SqPairLocal_adj_eq
import Theorems.Thm_P2M_PI_SqPairLocal_adj_eq__b8dc19b640ab

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
theorem _root_.solution {L' L'' : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E}
    (he' : Pres L' e) (he'' : Pres L'' e) (hg : Good Q c L' L'' e)
    (M : Matrix (Fin N) (Fin N) E)
    (hM : M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E))) :
    SmallAt Q c L' M ∧ SmallAt Q c L'' M := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  rcases hM with rfl | rfl | rfl
  · exact ⟨g1, g2⟩
  · rw [adj_eq]
    exact ⟨smallAt_add (smallAt_neg g1) (smallAt_mul g3 he'),
      smallAt_add (smallAt_neg g2) (smallAt_mul g4 he'')⟩
  · rw [adj_eq']
    exact ⟨smallAt_add (smallAt_neg g1) (smallAt_neg (smallAt_mul g3 (pres_one_sub he'))),
      smallAt_add (smallAt_neg g2) (smallAt_neg (smallAt_mul g4 (pres_one_sub he'')))⟩
end PI.SqPairLocal
