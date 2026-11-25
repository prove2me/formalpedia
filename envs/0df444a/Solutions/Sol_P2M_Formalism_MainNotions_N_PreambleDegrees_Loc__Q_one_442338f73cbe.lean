-- Prove2me | solution 1 for P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_one_442338f73cbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:03.362975+00:00
-- url     : https://prove2.me/submissions/39173c5f-8ec0-4601-81c8-8980244b91be

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots

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
theorem _root_.solution : ζQ l 1 ≠ 1 := by
  exact (exists_root_ne_one l).choose_spec.2
end Formalism.MainNotions.N.PreambleDegrees.Loc
