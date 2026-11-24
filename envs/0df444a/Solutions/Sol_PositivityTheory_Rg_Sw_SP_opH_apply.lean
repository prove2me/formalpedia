-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opH_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:33.044395+00:00
-- url     : https://prove2.me/submissions/13248170-2925-406e-bfcb-aff78d1e90f7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    opH s m b k l Q = (-(cc s b)) • (MvPolynomial.C (aa m b) * yv b l k * Q) +
      ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * pderiv (b, a, d) Q) := by
  cases b <;>
  simp only [opH, cc, aa, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Bool.false_eq_true, if_true, if_false]
end PositivityTheory.Rg.Sw.SP
