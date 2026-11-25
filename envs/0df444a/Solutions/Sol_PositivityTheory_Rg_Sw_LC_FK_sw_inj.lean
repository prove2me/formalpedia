-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.sw_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:26.89566+00:00
-- url     : https://prove2.me/submissions/f9c0a2d9-dcec-452a-83a8-cc5c63d1996a

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
theorem _root_.solution {k k' : Fin m × Fin n × Bool} : sw k = sw k' ↔ k = k' := by
  obtain ⟨a, i, b⟩ := k
  obtain ⟨a', i', b'⟩ := k'
  cases b <;> cases b' <;> simp [sw]
end PositivityTheory.Rg.Sw.LC.FK
