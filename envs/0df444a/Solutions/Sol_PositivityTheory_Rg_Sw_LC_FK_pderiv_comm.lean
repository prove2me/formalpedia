-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:46.542461+00:00
-- url     : https://prove2.me/submissions/0fac336c-8dae-43d8-96a3-646c8ecee202

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.FK
theorem _root_.solution (i j : Fin m × Fin n × Bool) (P : PX m n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅(pderiv (R := ℂ) i : Derivation ℂ (PX m n) (PX m n)), pderiv (R := ℂ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Pi.single_apply, hi, hj]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this
end PositivityTheory.Rg.Sw.LC.FK
