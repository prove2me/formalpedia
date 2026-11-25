-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:45.104606+00:00
-- url     : https://prove2.me/submissions/087878a1-fb6a-453b-9562-f44f78356c41

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detU
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detV
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_dPpow
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_evUV

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (cls s z p q R) :=
  (((contDiff_dPpow z).mul ((contDiff_detU hs).pow p)).mul ((contDiff_detV hs).pow q)).mul (contDiff_evUV hs R)
end PositivityTheory.Rg.Sw.WR.B
