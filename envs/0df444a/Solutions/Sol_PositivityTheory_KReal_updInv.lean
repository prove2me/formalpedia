-- Prove2me | solution 1 for PositivityTheory.KReal.updInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:25:32.53006+00:00
-- url     : https://prove2.me/submissions/66d4ff5c-4719-407b-b737-1c797ac82f64

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC

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
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
omit [Fintype I] [DecidableEq I] [Fintype J]
namespace PositivityTheory.KReal
theorem _root_.solution (s : J) : Function.Involutive
    (fun x : (J → I) × I => (Function.update x.1 s x.2, x.1 s)) := by
  rintro ⟨w, i⟩
  simp [Function.update_idem, Function.update_self, Function.update_eq_self]
end PositivityTheory.KReal
