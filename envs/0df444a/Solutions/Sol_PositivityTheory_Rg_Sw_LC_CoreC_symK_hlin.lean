-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.symK_hlin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:17.949206+00:00
-- url     : https://prove2.me/submissions/53d3ff5c-b24d-4c7c-a13c-02e760e094da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_expand_lin
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_symK_lin

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by
  obtain ⟨c, w0, h⟩ := symK_lin ε i j v
  rw [h]; exact expand_lin c w0
end PositivityTheory.Rg.Sw.LC.CoreC
