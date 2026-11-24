-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.entAn_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:35.408797+00:00
-- url     : https://prove2.me/submissions/7b13d27a-f26a-4b63-bc8e-af67fa3cde11

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_det

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
theorem _root_.solution {M : MC n → Matrix (Fin n) (Fin n) ℂ} {B₀ : MC n} (h : EntAn M B₀) (h0 : (M B₀).det ≠ 0) :
    EntAn (fun B => (M B)⁻¹) B₀ := by
  intro i j
  have e : (fun B => (M B)⁻¹ i j) = fun B => ((M B).det)⁻¹ * ((M B).updateRow j (Pi.single i 1)).det := by
    funext B
    rw [inv_def, Matrix.smul_apply, adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [e]
  refine ((an_det h).inv h0).mul (an_det fun a b => ?_)
  simp only [updateRow_apply]
  by_cases hab : a = j
  · simp only [hab, if_true]
    exact analyticAt_const
  · simp only [hab, if_false]
    exact h a b
end PositivityTheory.Rg.Sw.WR.Z
