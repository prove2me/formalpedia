-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.sec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:37.887431+00:00
-- url     : https://prove2.me/submissions/f8657626-ee91-4ab7-97a6-77b92ed03831

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_integ_sec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P Q : PX m n) : secN ε c t (P + Q) b = secN ε c t P b + secN ε c t Q b := by
  unfold secN
  rw [← integral_add (integ_sec hI hc hb P) (integ_sec hI hc hb Q)]
  congr 1; funext x; simp [evX]; ring
end PositivityTheory.Rg.Sw.WR.G.GM
