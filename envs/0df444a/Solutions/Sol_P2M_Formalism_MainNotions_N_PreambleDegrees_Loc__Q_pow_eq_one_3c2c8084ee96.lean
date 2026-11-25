-- Prove2me | solution 1 for P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_eq_one_3c2c8084ee96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:06:33.382324+00:00
-- url     : https://prove2.me/submissions/d0ac1dbc-4387-4c4b-a572-468202b3f144

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_zero_674fe5971222
import Theorems.Thm_P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_pow_103acde85a5f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.PreambleDegrees Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
variable (l)
namespace Formalism.MainNotions.N.PreambleDegrees.Loc
theorem _root_.solution (m : ℕ) : ζQ l m ^ (l ^ m) = 1 := by
  have h := ζQ_pow l 0 m
  rwa [zero_add, ζQ_zero] at h
end Formalism.MainNotions.N.PreambleDegrees.Loc
