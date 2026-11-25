-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.prod_sqrt_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:30.009919+00:00
-- url     : https://prove2.me/submissions/831c20ab-f79c-408e-9347-af8cf825bf1a

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by
  have h1 : ∀ k, Real.sqrt (w (σ k) * w k) = Real.sqrt (w (σ k)) * Real.sqrt (w k) := fun k =>
    Real.sqrt_mul (hw _).le _
  simp_rw [h1, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun k => Real.sqrt (w k)), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (hw k).le
end PositivityTheory.Rg.Sw.WR.K.GB
