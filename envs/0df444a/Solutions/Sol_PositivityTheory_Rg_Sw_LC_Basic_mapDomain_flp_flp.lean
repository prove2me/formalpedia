-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.mapDomain_flp_flp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:09.489832+00:00
-- url     : https://prove2.me/submissions/bbea9316-4196-4785-9010-acb4282ccaf4

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
theorem _root_.solution (t : Ix m n →₀ ℕ) : Finsupp.mapDomain flp (Finsupp.mapDomain flp t) = t := by
  rw [← Finsupp.mapDomain_comp]
  have : (flp ∘ flp : Ix m n → Ix m n) = id := funext flp_flp
  rw [this, Finsupp.mapDomain_id]
end PositivityTheory.Rg.Sw.LC.Basic
