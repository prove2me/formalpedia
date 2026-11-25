-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.diff_inv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:48.780551+00:00
-- url     : https://prove2.me/submissions/60c02e2c-0bb8-4f4e-8bc8-e9dd11207bd8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_hasDerivAt_line
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_mX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_X
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_entAn_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (x v : MC n) (h : (1 - (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_X (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mX s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt
end PositivityTheory.Rg.Sw.SP
