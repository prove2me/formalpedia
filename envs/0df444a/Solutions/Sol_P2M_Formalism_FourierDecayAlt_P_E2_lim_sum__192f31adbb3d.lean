-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:17.095945+00:00
-- url     : https://prove2.me/submissions/ccddc079-002b-4205-a101-a307344f1505

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_zero__0895612bcbef
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.E2
open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory
namespace Formalism.FourierDecayAlt.P.E2
theorem _root_.solution {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := h2 0 0 bdd_zero'
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1 _ _ (hf a) (bdd_sum' s f hf), ih]
end Formalism.FourierDecayAlt.P.E2
