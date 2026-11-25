-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.symK_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:20.445806+00:00
-- url     : https://prove2.me/submissions/c1cb4301-d93a-4791-8d71-4332207fe518

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symK_monomial_mem

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
theorem _root_.solution {N : ℕ} (i j : Fin n) {s : Sym m n} (hs : s ∈ S ε N) : symK ε i j s ∈ S ε N := by
  rw [as_sum s, map_sum]
  exact Submodule.sum_mem _ fun t ht => symK_monomial_mem i j (mem_S.1 hs t ht) _
end PositivityTheory.Rg.Sw.LC.CoreD
