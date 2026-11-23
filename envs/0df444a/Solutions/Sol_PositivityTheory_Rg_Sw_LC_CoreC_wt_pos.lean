-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.wt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:58.574037+00:00
-- url     : https://prove2.me/submissions/6e46baa2-949e-4e2d-aac4-adaf9954714b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution {c : ℝ} (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) : 0 < wt c s := by
  rw [wt_univ]
  exact Finset.prod_pos fun k _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by linarith) _)
end PositivityTheory.Rg.Sw.LC.CoreC
