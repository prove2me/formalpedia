-- Prove2me | solution 1 for PI.HeckeProdW.no_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:05.783617+00:00
-- url     : https://prove2.me/submissions/54c67b03-587c-47cd-be4a-d26cce8011ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Theorems.Thm_Bl_SecondBlockLemmaN_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
namespace PI.HeckeProdW
theorem _root_.solution (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first | exact Bl.SecondBlockLemmaN.goal1 .. | (apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaN.goal1 z h | exact @Bl.SecondBlockLemmaN.goal1 z
end PI.HeckeProdW
