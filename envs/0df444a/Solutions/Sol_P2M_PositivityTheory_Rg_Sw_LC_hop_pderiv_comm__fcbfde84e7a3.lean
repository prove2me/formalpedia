-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:53.663497+00:00
-- url     : https://prove2.me/submissions/7746b7d9-d37e-40b0-83f3-e3722f0c0dad

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by
  have h : (⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this
end PositivityTheory.Rg.Sw.LC
