-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__example_weights_injective_4d5356484bd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:42.33805+00:00
-- url     : https://prove2.me/submissions/97d954e6-7a06-49c9-9aa7-6a9229d0cae4

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
theorem _root_.solution : Function.Injective fun x : Fin 2 × Fin 2 => l4 x.1 x.2 := by
  rintro ⟨j, p⟩ ⟨j', p'⟩ h
  fin_cases j <;> fin_cases p <;> fin_cases j' <;> fin_cases p' <;> simp [l4] at h ⊢ <;> norm_num at h
end Formalism.L2.Indef.Examples₂
