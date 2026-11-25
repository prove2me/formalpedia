-- Prove2me | solution 1 for PI.LevelKSplit.W.Split.levelSAll_of_existS_measKf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:29.081035+00:00
-- url     : https://prove2.me/submissions/f405451d-913c-4ab3-82e9-5729acc06908

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Theorems.Thm_PI_LevelKSplit_W_Split_level_split_all
import Theorems.Thm_PI_LevelKSplit_W_levelSAll_of


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
theorem _root_.solution (h1 : ExistSAll) (h2 : MeasKfAll) : LevelSAll :=
  levelSAll_of h1 h2 level_split_all
end PI.LevelKSplit.W.Split
