-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.det_corner_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:39.341738+00:00
-- url     : https://prove2.me/submissions/69d5ebc1-62e8-4dc2-a959-a969aaccc9fb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_phiL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_piL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_det_first_row_expansion
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
theorem _root_.solution (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    (1 + phiF X + s • Matrix.single 0 0 1).det = (1 + s) * (1 + piF X).det := by
  have hsub : (1 + phiF X + s • Matrix.single 0 0 1).submatrix Fin.succ Fin.succ = 1 + piF X := by
    ext k l
    simp [piF, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj, Fin.succ_ne_zero]
    intro h; exact absurd h.symm (Fin.succ_ne_zero k)
  rw [det_first_row_expansion _ (1 + s), hsub]
  intro j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp [Matrix.one_apply, Matrix.single_apply]
  · simp [Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero m).symm]
end PositivityTheory.Rg.Sw.LVs.CK
