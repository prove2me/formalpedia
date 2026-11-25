-- Prove2me | solution 1 for PIW.CMDiscSq.exists_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:08.505026+00:00
-- url     : https://prove2.me/submissions/50c3e518-e564-4843-b31f-2e6c2f52598f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_FinrankTwoOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ x : E, star x ≠ x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P hP
  refine ⟨algebraMap (𝓞 E) E θ, ?_⟩
  rw [← ht]
  intro h
  apply hθ
  have : t = θ := RingOfIntegers.coe_injective h
  rw [this, sub_self]
  exact P.zero_mem
end PIW.CMDiscSq
