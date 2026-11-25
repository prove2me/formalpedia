-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.symK_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:21.854113+00:00
-- url     : https://prove2.me/submissions/f06327f6-dcbc-412a-a2c4-e49f7230ccb6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_X

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
    symK ε i j (X (Sum.inl k)) = rename Sum.inl (KopL ε i j (X k)) := by
  rw [symK, mkDerivation_X, Sum.elim_inl, KopL_X]
  split_ifs <;> simp
end PositivityTheory.Rg.Sw.LC.CoreBb
