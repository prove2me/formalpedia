-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.piF_single_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:22.272979+00:00
-- url     : https://prove2.me/submissions/b2b8b808-6f17-45c3-9563-2523e57b70b8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.phiL_apply
attribute [local simp] PositivityTheory.Rg.Sw.LVs.CK.piL_apply

set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (k : Fin N) : piF (Matrix.single k (0 : Fin (N + 1)) (1 : ℂ)) = 0 := by
  ext a b; simp only [piF, Matrix.single_apply, Matrix.zero_apply]
  rw [if_neg]; rintro ⟨_, h⟩; exact Fin.succ_ne_zero b h.symm
end PositivityTheory.Rg.Sw.LVs.CK
