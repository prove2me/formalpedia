-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.conj_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:29.445079+00:00
-- url     : https://prove2.me/submissions/7e890eba-9a30-4894-ae7a-a56b03645d0c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution (k : Mc n) (p : Fin n × Fin n) (c d : Fin n) :
    (k * E p * kᴴ) c d = k c p.1 * (k.map star) d p.2 := by
  simp [E, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
