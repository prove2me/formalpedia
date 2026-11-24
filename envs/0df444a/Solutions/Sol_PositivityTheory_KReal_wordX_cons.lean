-- Prove2me | solution 1 for PositivityTheory.KReal.wordX_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.06082+00:00
-- url     : https://prove2.me/submissions/a30b5f10-4f27-4832-8de9-807f6386ae50

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (X : I → Module.End ℂ M) (a : I) (l : List I) (y : M) :
    wordX X (a :: l) y = X a (wordX X l y) := by
  simp [wordX]
end PositivityTheory.KReal
