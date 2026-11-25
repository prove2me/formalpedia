-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.symK_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:04.894963+00:00
-- url     : https://prove2.me/submissions/b11eb98f-ec21-4ad8-b7a3-e877f6a3c1b8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> rcases u with ⟨a', i'', b'⟩ | ⟨a', i'', b'⟩ <;>
    simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp_all [coeff_X', Finsupp.single_left_inj, coeff_neg] <;> aesop
end PositivityTheory.Rg.Sw.LC.CoreC
