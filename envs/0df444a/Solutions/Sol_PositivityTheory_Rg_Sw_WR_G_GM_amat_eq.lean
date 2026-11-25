-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.amat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:19.141948+00:00
-- url     : https://prove2.me/submissions/883f6ce9-9f9d-4166-9351-e9fd2e19fad9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_sgn_eq

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
theorem _root_.solution (ε : Fin m → Bool) (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) :
    Amat ε c (s * c) b a = (c : ℂ) • (Mm ε s b a)ᵀ := by
  unfold Amat Mm
  rw [transpose_sub, transpose_one, transpose_smul, smul_sub, smul_smul, sgn_eq]
  congr 2
  push_cast; ring
end PositivityTheory.Rg.Sw.WR.G.GM
