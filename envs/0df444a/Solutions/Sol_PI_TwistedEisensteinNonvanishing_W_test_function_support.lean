-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.test_function_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:54.139282+00:00
-- url     : https://prove2.me/submissions/6b8b1b4c-3fa5-4a75-a4a9-08d7076657f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_eN_out

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
theorem _root_.solution : PhiSuppP := by
  intro E K _ _ _ _ P q ξ k₀ r c' n' c n hk hk' y hy s l
  have hc : ∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 y p p') := by
    by_contra hc
    apply hy
    unfold PhiQ
    rw [if_neg (fun h => hc h.1)]
  by_cases hs : s < n' + c'
  · have h1 := hc _ _ (fPos_lt' hk l.2) (fPos_lt' hk' hs)
    simpa [entB, scE, fIdx_fPos' hk l.2, fIdx_fPos' hk' hs, atN, l.2] using h1
  · rw [eN_out (E := E) hs, map_zero]
    exact ⟨0, 1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
end PI.TwistedEisensteinNonvanishing.W
