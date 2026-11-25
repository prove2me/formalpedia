-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.coe_phi_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:55.994116+00:00
-- url     : https://prove2.me/submissions/431dda85-8d43-4628-ae57-3052b32d15d1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (s : Ix m n →₀ ℕ) :
    ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) =
      ((Finset.univ : Finset (Ix m n)).toList.map fun k => (cr c k) ^ (s k)).prod := by
  rw [phi, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_map_toList]
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  congr 1
end PositivityTheory.Rg.Sw.LC.Basic
