-- Prove2me | solution 1 for P2M_Formalism_L2_Col_HXm_eq_map__8e8b55c128f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:08.950131+00:00
-- url     : https://prove2.me/submissions/5b113ae1-fac9-4b6d-9c56-e7fcbea3baf5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_HXm_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (n' r t m : ℕ) (hn : n' = r + m * t) :
    HXm κ (n' + 1) r t m = (HJ κ n' r t m).map (diagEmb κ (Nat.le_succ n')) := by
  subst hn
  exact HXm_eq_map r t m
end Formalism.L2.Col
