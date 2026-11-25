-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:13.240652+00:00
-- url     : https://prove2.me/submissions/76b63aa7-5627-4c8e-8c26-82dfa3662a38

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detU
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detV
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detU
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detV
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_pow
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_dPpow
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_dPpow
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_evUV_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_evUV
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_evUV
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of
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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (y : E n) (k l : Fin n) : dirC (cls s z p q R) (vkl k l) y = cls s z p q (dR s z p q k l R) y := by
  have h1 := diffAt_of (contDiff_dPpow (n := n) z) y
  have h2 := diffAt_of ((contDiff_detU (n := n) hs).pow p) y
  have h3 := diffAt_of ((contDiff_detV (n := n) hs).pow q) y
  have h4 := diffAt_of (contDiff_evUV hs R) y
  rw [show cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q * evUV s R y from rfl]
  rw [dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q) (g := evUV s R)
      ((h1.mul h2).mul h3) h4,
    dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p) (g := fun y => (vM s y).det ^ q)
      (h1.mul h2) h3,
    dirC_mul (f := fun y => ((dP y : ℝ) : ℂ) ^ (-z)) (g := fun y => (uM s y).det ^ p) h1 h2, dirC_dPpow hs,
    dirC_pow (diffAt_of (contDiff_detU hs) y) p _ _ (dirC_detU hs y k l),
    dirC_pow (diffAt_of (contDiff_detV hs) y) q _ (-(Complex.I * s * vM s y k l)) (by rw [dirC_detV hs]; ring),
    dirC_evUV hs]
  simp only [cls, dR, evUV_eq, map_add, map_mul, map_sub, eval_C, eval_X, ent]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring
end PositivityTheory.Rg.Sw.WR.B
