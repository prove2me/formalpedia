-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.kopL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:19.443738+00:00
-- url     : https://prove2.me/submissions/d08e2d9d-d49f-4fa2-aec4-491645b2599f

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by
  simp [KopL]
end PositivityTheory.Rg.Sw.LC.FK
