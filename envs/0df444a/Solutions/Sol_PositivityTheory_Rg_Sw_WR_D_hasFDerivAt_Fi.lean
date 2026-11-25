-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.hasFDerivAt_Fi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:25.830582+00:00
-- url     : https://prove2.me/submissions/cadb1a7b-4970-40b1-8792-193959ae3797

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Lc_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
variable (ε : Fin m → Bool) (c t : ℝ)
variable {ε c t}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => Fi ε c t P y x) (Fd ε c t P y x) y := by
  have h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y := by
    have : (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y :=
      funext fun y => (Lc_apply _ y).symm
    rw [this]; exact (Lc (qX ε x)).hasFDerivAt
  have h2 := (h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)
  have e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x)
      = Fd ε c t P y x := by
    rw [Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]
  exact h2.congr_fderiv e
end PositivityTheory.Rg.Sw.WR.D
