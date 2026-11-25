-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:45.933575+00:00
-- url     : https://prove2.me/submissions/a3cbcee2-845b-40ae-8cee-098bff0f1693

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealLatticeFG
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_idealLattice_eq_iSup_4b66f2df994c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
namespace GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
theorem _root_.solution (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by
  rw [idealLattice_eq_iSup]
  exact Submodule.fg_iSup _ fun x =>
    ((a x).fg_of_isNoetherianRing le_rfl).map _
end GroundTheory.Heights₂.Heights.KLinesIdealLatticeFG
