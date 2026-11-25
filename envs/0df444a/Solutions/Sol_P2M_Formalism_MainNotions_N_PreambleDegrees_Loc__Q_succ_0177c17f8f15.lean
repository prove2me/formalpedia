-- Prove2me | solution 1 for P2M_Formalism_MainNotions_N_PreambleDegrees_Loc__Q_succ_0177c17f8f15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:23:38.683529+00:00
-- url     : https://prove2.me/submissions/87f5bfe7-5c14-4d38-8670-71bfcb07e7a6

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
theorem _root_.solution (m : ℕ) : ζQ l (m + 1) ^ l = ζQ l m := by
  cases m with
  | zero => exact (exists_root_ne_one l).choose_spec.1
  | succ m => exact (exists_root l (ζQ l (m + 1))).choose_spec
end Formalism.MainNotions.N.PreambleDegrees.Loc
