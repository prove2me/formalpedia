-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.castLE_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:36.739818+00:00
-- url     : https://prove2.me/submissions/a6829f2e-b283-4b01-8ae9-6145a5c95dfe

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {N m : ℕ} (hm : m ≤ N) {i j : Fin m} (h : i ≤ j) :
    Fin.castLE hm i ≤ Fin.castLE hm j :=
  Fin.le_iff_val_le_val.2 (by simpa using Fin.le_iff_val_le_val.1 h)
end ReciprocityTheory.AnForm.P
