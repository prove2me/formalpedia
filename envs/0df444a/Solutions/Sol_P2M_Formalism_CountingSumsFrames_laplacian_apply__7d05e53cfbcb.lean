-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_laplacian_apply__7d05e53cfbcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:44.127695+00:00
-- url     : https://prove2.me/submissions/f9808952-ee8c-4499-9605-f637e5999ef7

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  simp [ctrF, LinearMap.sum_apply]
end Formalism.CountingSumsFrames
