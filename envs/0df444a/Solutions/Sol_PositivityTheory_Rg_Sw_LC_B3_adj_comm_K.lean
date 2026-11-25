-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.adj_comm_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:26.794404+00:00
-- url     : https://prove2.me/submissions/536c5dbd-3429-430a-b28b-35b8d06ac4d2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_pair_comm_K

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) {w : Module.End ℂ (PX m n)} (hw : w ∈ PA ε) :
    w * KopL ε i j = KopL ε i j * w := by
  have hle : PA (n := n) ε ≤ Subalgebra.centralizer ℂ {KopL ε i j} := by
    apply Algebra.adjoin_le
    rintro _ ⟨ab, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (pair_comm_K ε ab.1 ab.2 i j).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) _ (Set.mem_singleton _)).symm
end PositivityTheory.Rg.Sw.LC.B3
