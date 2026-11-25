-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.proj_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:18.493048+00:00
-- url     : https://prove2.me/submissions/f442f322-7a5c-4f01-a7af-26cc2092d5c0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
theorem _root_.solution {J : Matrix ι ι ℂ} {d : ℂ} (hd : J * J = d • 1) (hd0 : d ≠ 0) {Y : Matrix ι ι ℂ} (hY : InLie J Y) :
    proj J d ((1 / 2 : ℂ) • Y) = Y := by
  have h1 : J * Yᴴ * J = -(d • Y) := by
    have h2 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  unfold proj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, h1]
  ext i j
  simp
  field_simp
  ring
end PositivityTheory.SiegelWeilFormula.Krd.DC
