-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.conj_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:27.462151+00:00
-- url     : https://prove2.me/submissions/7c7de347-de44-4045-ae87-5218aff89d27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Mc n) : (k * A * kᴴ).det = A.det := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (k.det), mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]
end PositivityTheory.Rg.Sw.WR.K.GB
