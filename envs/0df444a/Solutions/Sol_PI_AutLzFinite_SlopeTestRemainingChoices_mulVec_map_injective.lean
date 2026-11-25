-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.mulVec_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:14.935433+00:00
-- url     : https://prove2.me/submissions/4bcc2fff-76e8-48e8-b22c-ef3b2d6a5168

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Theorems.Thm_Bl_general_b_fact_upper_alt_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution {K : Type} [Field K] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k]
    [DecidableEq k] (f : K →+* ℂ) (A : Matrix n k K) (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map f).mulVec := by
  first | exact Bl.general_b_fact_upper_alt_form.goal1 .. | (apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A hA | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K
end PI.AutLzFinite.SlopeTestRemainingChoices
