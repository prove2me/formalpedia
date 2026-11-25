-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.psi_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:40.492426+00:00
-- url     : https://prove2.me/submissions/7de5645b-dd42-47e4-b15f-e8901d95bcb5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D : ℕ}
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) (z : E) : psi z ≠ 0 := by
  obtain ⟨hmul, hint, hout⟩ := hpsi
  by_cases hz : IntAt P ((qOf P : E) ^ D * z)
  · have hz' : IntAt P ((qOf P : E) ^ D * (-z)) := by
      obtain ⟨r, s, hs, hrs⟩ := hz
      exact ⟨-r, s, hs, by rw [mul_neg, mul_neg, hrs, map_neg]⟩
    have h0 : IntAt P 0 := ⟨0, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
    have h := hmul z (-z) hz hz'
    rw [add_neg_cancel, hint 0 h0] at h
    intro hz0
    rw [hz0, zero_mul] at h
    exact one_ne_zero h
  · rw [hout z hz]
    exact one_ne_zero
end PI.TwistedEisensteinNonvanishing.W
