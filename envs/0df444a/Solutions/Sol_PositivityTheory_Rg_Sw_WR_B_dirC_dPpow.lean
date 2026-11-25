-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_dPpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:55.953711+00:00
-- url     : https://prove2.me/submissions/bb4974fb-7779-4174-aa2b-49922799bae0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dP_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (y : E n) (k l : Fin n) :
    dirC (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) (vkl k l) y =
      Complex.I * s * z * (uM s y k l - vM s y k l) * ((dP y : ℝ) : ℂ) ^ (-z) := by
  have hmem : ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr (dP_pos y)
  have hne : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (dP_pos y).ne'
  have hPd : DifferentiableAt ℝ (fun y : E n => (Bm s y).det * (Am s y).det) y :=
    (diffAt_of (contDiff_detBm s) y).mul (diffAt_of (contDiff_detAm s) y)
  have e : (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z)) = fun y => ((Bm s y).det * (Am s y).det) ^ (-z) :=
    funext fun y => by rw [dP_eq hs]
  rw [e]
  rw [dP_eq hs] at hmem
  rw [dirC_comp (Complex.hasStrictDerivAt_cpow_const hmem).hasDerivAt hPd,
    dirC_mul (diffAt_of (contDiff_detBm s) y) (diffAt_of (contDiff_detAm s) y), dirC_detAm hs, dirC_detBm hs,
    ← dP_eq hs, Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rw [show ((Bm s y).det * (-(Complex.I * s) * (Am s y).det * uM s y k l) +
      (Am s y).det * (Complex.I * s * (Bm s y).det * vM s y k l)) =
      -(Complex.I * s) * ((Bm s y).det * (Am s y).det) * (uM s y k l - vM s y k l) by ring, ← dP_eq hs]
  field_simp <;> ring
end PositivityTheory.Rg.Sw.WR.B
