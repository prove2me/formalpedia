-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.lin_lf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:53.784795+00:00
-- url     : https://prove2.me/submissions/26328bab-28ef-4187-9fb5-cf88aa38eb68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (φ : PX m n →ₗ[ℂ] PX m n) (b : Bool) (N M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n)
    (h : ∀ c, φ (X (c, i, b)) = lf b N c i) : φ (lf b M a i) = lf b (M * N) a i := by
  simp only [lf, C_mul', map_sum, map_smul, h, Finset.smul_sum, smul_smul, mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => C_mul'.symm
end PositivityTheory.SiegelWeilFormula.KSplit
