-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:55.385609+00:00
-- url     : https://prove2.me/submissions/813cc0e5-b03d-4c47-9410-19d867e424ad

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_add__5580613dd956
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_zero__0895612bcbef

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
theorem _root_.solution {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using bdd_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact bdd_add' (hf a) ih
end Formalism.FourierDecayAlt.P.E2
