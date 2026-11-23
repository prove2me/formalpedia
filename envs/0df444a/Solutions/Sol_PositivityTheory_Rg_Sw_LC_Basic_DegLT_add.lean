-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.DegLT.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:59.504664+00:00
-- url     : https://prove2.me/submissions/5110d600-006c-48e0-915d-f94aac6a8a12

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
namespace DegLT
theorem _root_.solution {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P + Q) := by
  classical
  intro t ht
  rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
  · exact hP t h
  · exact hQ t h
end DegLT
end PositivityTheory.Rg.Sw.LC.Basic
