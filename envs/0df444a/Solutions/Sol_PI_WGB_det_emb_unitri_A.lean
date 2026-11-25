-- Prove2me | solution 1 for PI.WGB.det_emb_unitri_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:20.366417+00:00
-- url     : https://prove2.me/submissions/e2f02243-5920-475f-b388-19bd23e8a9c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_UpperTheory_Reformulated_B_Qe13_det_emb_unitri_A


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := by
  first | exact UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A .. | (apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl hd | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g hl | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n g | exact @UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A n
end PI.WGB
