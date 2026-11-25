-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.PA_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:21.231123+00:00
-- url     : https://prove2.me/submissions/56925b3b-42bd-48e6-a4e9-7dac5221ddfc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_opL_pair

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
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (hc : c ≠ 0) :
    PA (n := n) ε ≤ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2) := by
  apply Algebra.adjoin_le
  rintro _ ⟨ab, rfl⟩
  obtain ⟨κ, hκ⟩ := opL_pair (n := n) ε c hc ab.1 ab.2
  rw [SetLike.mem_coe]
  simp only
  rw [hκ]
  exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self ab)) κ
end PositivityTheory.Rg.Sw.LC.B3
