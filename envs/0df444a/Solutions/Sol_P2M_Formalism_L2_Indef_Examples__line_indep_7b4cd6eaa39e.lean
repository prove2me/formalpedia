-- Prove2me | solution 1 for P2M_Formalism_L2_Indef_Examples__line_indep_7b4cd6eaa39e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:24:59.999858+00:00
-- url     : https://prove2.me/submissions/fe0b4d84-6cb0-4cde-8534-b08eef54f06f

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
theorem _root_.solution (n : ℕ) : iSupIndep (line K n) := by
  intro i
  have h := LinearMap.disjoint_single_single K (fun _ : Fin n => K) {i} {j | j ≠ i}
    (by simp)
  simpa [line] using h
end Formalism.L2.Indef.Examples₂
