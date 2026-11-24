-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.CommPf.smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:40.183395+00:00
-- url     : https://prove2.me/submissions/6cd107a4-8e2a-46ac-bd47-992ee1592444

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DerivationConstantVanishes

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
open PositivityTheory.Rg.Sw.SP.CommPf
namespace PositivityTheory.Rg.Sw.SP.CommPf
theorem _root_.solution (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl
end PositivityTheory.Rg.Sw.SP.CommPf
