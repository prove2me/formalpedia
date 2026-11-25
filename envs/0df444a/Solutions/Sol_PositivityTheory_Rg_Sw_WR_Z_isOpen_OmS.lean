-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.isOpen_OmS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:15.457804+00:00
-- url     : https://prove2.me/submissions/2b3b1b7e-8613-41db-96df-47498faf33b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (s : ℂ) : IsOpen (OmS (n := n) s) := by
  have g1 : Continuous fun B : MC n => 1 - (Complex.I * s) • Matrix.of B :=
    continuous_matrix fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      exact continuous_const.sub (continuous_const.mul (continuous_apply_apply i j))
  have g2 : Continuous fun B : MC n => 1 + (Complex.I * s) • Matrix.of B :=
    continuous_matrix fun i j => by
      simp only [Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      exact continuous_const.add (continuous_const.mul (continuous_apply_apply i j))
  have g3 : Continuous fun B : MC n => 1 + Matrix.of B * Matrix.of B :=
    continuous_const.add (continuous_of'.mul continuous_of')
  have h1 : Continuous fun B : MC n => (1 - (Complex.I * s) • Matrix.of B).det := g1.matrix_det
  have h2 : Continuous fun B : MC n => (1 + (Complex.I * s) • Matrix.of B).det := g2.matrix_det
  have h3 : Continuous fun B : MC n => (1 + Matrix.of B * Matrix.of B).det := g3.matrix_det
  have e : OmS (n := n) s = {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0} ∩
      ({B | (1 + (Complex.I * s) • Matrix.of B).det ≠ 0} ∩
        (fun B : MC n => (1 + Matrix.of B * Matrix.of B).det) ⁻¹' Complex.slitPlane) := rfl
  rw [e]
  exact (isOpen_ne_fun h1 continuous_const).inter ((isOpen_ne_fun h2 continuous_const).inter
    (Complex.isOpen_slitPlane.preimage h3))
end PositivityTheory.Rg.Sw.WR.Z
