-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.inLie_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:06.220603+00:00
-- url     : https://prove2.me/submissions/5610ba5f-5bdc-48e3-9056-2e71d86b1bbc

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
theorem _root_.solution {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) (Y : Matrix ι ι ℂ) : InLie J (proj J d Y) := by
  have hJJ : ∀ X : Matrix ι ι ℂ, J * (J * X) = d • X := by
    intro X
    rw [← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  have hsd : star d⁻¹ = d⁻¹ := by rw [star_inv₀, hds]
  unfold InLie proj
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hc, hsd]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, hJJ, hd, Matrix.mul_one]
  rw [hcc, mul_one, inv_mul_cancel₀ hd0, one_smul, one_smul]
  abel
end PositivityTheory.SiegelWeilFormula.Krd.DC
