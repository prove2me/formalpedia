-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.sq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:40.55722+00:00
-- url     : https://prove2.me/submissions/41b075e6-5b93-4843-b42b-87bb17ae426b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA

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
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (b : Matrix (Fin n) (Fin n) ℂ) :
    (1 - (Complex.I * s) • b) * (1 + (Complex.I * s) • b) = 1 + b * b := by
  have hc : (Complex.I * s) * (Complex.I * s) = -1 := by
    rcases hs with rfl | rfl <;> ring_nf <;> simp [Complex.I_sq]
  rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hc]
  simp only [neg_smul, one_smul]
  abel
end PositivityTheory.Rg.Sw.WR.Z
