-- Prove2me | solution 1 for PI.LevelKSplit.W.Split.level_split_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:02.220241+00:00
-- url     : https://prove2.me/submissions/84b2ef53-2f4d-48e3-9dcd-b566f5b0991c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Theorems.Thm_PI_LevelKSplit_W_Split_splitK_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Split
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.Split
theorem _root_.solution : SplitKAll := by
  intro F E _ _ _ _ _ σ _ M J _
  exact splitK_level
end PI.LevelKSplit.W.Split
