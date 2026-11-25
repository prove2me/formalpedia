-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.symK_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:40:42.522071+00:00
-- url     : https://prove2.me/submissions/b919a1ca-f480-400a-8b91-03a5e7224656

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    symK ε i j (X (Sum.inr k)) = if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -X (Sum.inr (k.1, j, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then X (Sum.inr (k.1, i, true)) else 0) := by
  rw [symK, mkDerivation_X, Sum.elim_inr]
end PositivityTheory.Rg.Sw.LC.CoreBb
