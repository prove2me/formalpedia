-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.monomial_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:24.546111+00:00
-- url     : https://prove2.me/submissions/86696be7-0aa0-40d9-95ba-53a7ddc14401

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem

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
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution {N : ℕ} {u} (hu : u ∈ U ε N) (r : ℂ) : monomial u r ∈ S (n := n) ε N := by
  refine mem_S.2 fun t ht => ?_
  have := support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  exact this ▸ hu
end PositivityTheory.Rg.Sw.LC.CoreD
