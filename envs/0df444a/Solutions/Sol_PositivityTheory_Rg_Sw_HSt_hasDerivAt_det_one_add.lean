-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.hasDerivAt_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:07.89278+00:00
-- url     : https://prove2.me/submissions/da0f5965-b4ea-45b5-80ac-9140b84871d1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_HasDerivAtDetOneAdd

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • M).det) M.trace 0 := by
  set p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det with hp
  have e : (fun s : ℂ => (1 + s • M).det) = fun s => p.eval s := by
    funext s
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp [mul_comm]
  rw [e]
  have h := p.hasDerivAt 0
  rwa [hp, Matrix.derivative_det_one_add_X_smul] at h
end PositivityTheory.Rg.Sw.HSt
