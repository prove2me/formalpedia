-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.sec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:17.536386+00:00
-- url     : https://prove2.me/submissions/76618cbe-0672-46b1-82c8-8ede23e344a7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM

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
theorem _root_.solution {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (r : ℂ) (P : PX m n) :
    secN ε c t (r • P) b = r * secN ε c t P b := by
  unfold secN
  rw [← integral_const_mul]
  congr 1; funext x; simp [evX, smul_eq_C_mul]; ring
end PositivityTheory.Rg.Sw.WR.G.GM
