-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.variable_mul_mem_first_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:20.283948+00:00
-- url     : https://prove2.me/submissions/6b060c00-4f11-475f-8ef4-91a90c6da95c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily

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
theorem _root_.solution (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : X k * p ∈ F1 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp
end PositivityTheory.Rg.Sw.LC.CoreC
