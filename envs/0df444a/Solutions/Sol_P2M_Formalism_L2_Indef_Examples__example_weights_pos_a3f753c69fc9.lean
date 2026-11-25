-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__example_weights_pos_a3f753c69fc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:59.592046+00:00
-- url     : https://prove2.me/submissions/d27ef76f-2d0f-4e86-acf3-d0f282f0974c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution (j p : Fin 2) : 0 < l4 j p := by unfold l4; positivity
end Formalism.L2.Indef.Examples₂
