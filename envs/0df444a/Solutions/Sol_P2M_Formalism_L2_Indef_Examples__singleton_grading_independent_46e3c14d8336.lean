-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__singleton_grading_independent_46e3c14d8336
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:57.176233+00:00
-- url     : https://prove2.me/submissions/96867bf2-cb9d-4a4a-8e15-2679ae46f7b6

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef.Examples₂
theorem _root_.solution (V : Type) [AddCommGroup V] [Module K V] : iSupIndep (only0 (K := K) V) := by
  rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (by intro k; fin_cases k <;> simp)]
  simp [only0]
end Formalism.L2.Indef.Examples₂
