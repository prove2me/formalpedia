-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.first_family_le_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:59.186865+00:00
-- url     : https://prove2.me/submissions/0ccf5dfb-cef4-4980-b931-0e5760cfad57

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (ε : Fin m → Bool) : F1 (n := n) ε ≤ box ε Set.univ := by
  intro p hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hF : ∀ k ∈ s.support, inF1 ε k := by
    intro k hk
    have : k ∈ p.vars := by
      rw [mem_vars]; exact ⟨s, hs, hk⟩
    exact (mem_supported.mp hp) this
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hF, Set.mem_univ _, rfl⟩)
end PositivityTheory.Rg.Sw.LC.Core
