-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBF_polyAction_one__8750f858715c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:07:46.360808+00:00
-- url     : https://prove2.me/submissions/f026428e-93eb-43d5-b3ce-96ae93a60619

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_zero_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_one_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.PBF
theorem _root_.solution (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by
  funext a
  unfold actP
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, pr_one_fst]
    rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), pr_zero_fst]
    rfl
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.PBF
