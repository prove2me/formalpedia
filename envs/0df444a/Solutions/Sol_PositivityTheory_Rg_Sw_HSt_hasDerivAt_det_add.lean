-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.hasDerivAt_det_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:54.791801+00:00
-- url     : https://prove2.me/submissions/0f645bb4-3416-492e-b2de-d6c231f2e138

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_HasDerivAtDetOneAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_hasDerivAt_det_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
namespace PositivityTheory.Rg.Sw.HSt
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℂ => (A + s • X).det) (A.det * (A⁻¹ * X).trace) 0 := by
  have e : (fun s : ℂ => (A + s • X).det) = fun s => A.det * (1 + s • (A⁻¹ * X)).det := by
    funext s
    rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [e]
  exact (hasDerivAt_det_one_add (A⁻¹ * X)).const_mul _
end PositivityTheory.Rg.Sw.HSt
