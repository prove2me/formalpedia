-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.mem_S_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:48.759502+00:00
-- url     : https://prove2.me/submissions/d55ee52c-10ca-4443-866c-a2fdc64faaf4

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
theorem _root_.solution {s : Sym m n} (h : SymbolInFirstFamily ε s) : s ∈ S ε s.totalDegree := by
  refine mem_S.2 fun t ht => ⟨le_totalDegree ht, fun v hv => ?_⟩
  rcases v with k | k
  · exact h t ht k (Or.inl (Finsupp.mem_support_iff.1 hv))
  · exact h t ht k (Or.inr (Finsupp.mem_support_iff.1 hv))
end PositivityTheory.Rg.Sw.LC.CoreD
