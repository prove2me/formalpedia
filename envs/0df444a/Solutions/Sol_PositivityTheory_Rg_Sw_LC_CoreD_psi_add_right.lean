-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.psi_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:42.959583+00:00
-- url     : https://prove2.me/submissions/f2022acb-23c1-4f33-95a8-ecffabe6d4e3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_psi_eq

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
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution (p q₁ q₂ : Sym m n) : psi p (q₁ + q₂) = psi p q₁ + psi p q₂ := by
  classical
  have h0 : (q₁ + q₂).support ⊆ q₁.support ∪ q₂.support := support_add
  rw [psi_eq p (q₁ + q₂) (p.support ∪ q₁.support ∪ q₂.support) (by
      intro u hu; rcases Finset.mem_union.1 hu with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · rcases Finset.mem_union.1 (h0 h) with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'),
    psi_eq p q₁ (p.support ∪ q₁.support ∪ q₂.support) (Finset.union_subset_left le_rfl),
    psi_eq p q₂ (p.support ∪ q₁.support ∪ q₂.support)
      (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_add]; ring
end PositivityTheory.Rg.Sw.LC.CoreD
