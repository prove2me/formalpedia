-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.fsum_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:10.341795+00:00
-- url     : https://prove2.me/submissions/faff7b5e-86f8-439f-92eb-0c72ad6273fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivFsum
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
theorem _root_.solution (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsum t c (y + s • Matrix.single k0 0 1) =
      fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hp : piF (y + s • Matrix.single k0 0 1) = piF y := by
    ext k l
    simp [piF, Matrix.single_apply, Fin.succ_ne_zero]
    intro _ h
    exact absurd h.symm (Fin.succ_ne_zero l)
  simp only [fsum, hp]
  (simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']) <;> ring
end PositivityTheory.Rg.Sw.LVs.CK
