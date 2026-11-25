-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.symK_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:41:46.342528+00:00
-- url     : https://prove2.me/submissions/f543dab4-0ca4-4dec-8935-390b0e02b432

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (v) :
    ∃ (c : ℂ) (w0 : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)), symK ε i j (X v : Sym m n) = c • X w0 := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;>
    first
    | exact ⟨1, _, (one_smul _ _).symm⟩
    | exact ⟨-1, _, by rw [neg_smul, one_smul]⟩
    | exact ⟨0, Sum.inl (a, i', b), (zero_smul _ _).symm⟩
end PositivityTheory.Rg.Sw.LC.CoreC
