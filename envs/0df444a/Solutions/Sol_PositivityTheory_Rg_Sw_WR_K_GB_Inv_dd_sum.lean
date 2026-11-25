-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:24.689305+00:00
-- url     : https://prove2.me/submissions/8965c410-47b0-43b1-8fd0-b5135f941ee7

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → Mc n → ℂ) (H : Mc n) {x : Mc n}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) :
    dd H (fun y => ∑ i ∈ s, a i * g i y) x = ∑ i ∈ s, a i * dd H (g i) x := by
  unfold dd
  have h : HasFDerivAt (fun y => ∑ i ∈ s, a i * g i y) (∑ i ∈ s, a i • fderiv ℂ (g i) x) x :=
    HasFDerivAt.fun_sum fun i hi => (hg i hi).hasFDerivAt.const_mul (a i)
  rw [h.fderiv]
  simp
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
