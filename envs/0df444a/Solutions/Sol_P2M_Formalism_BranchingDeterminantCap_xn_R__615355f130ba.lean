-- Prove2me | solution 1 for P2M_Formalism_BranchingDeterminantCap_xn_R__615355f130ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:31.399445+00:00
-- url     : https://prove2.me/submissions/87644b15-cfe4-429e-857e-9ba17cf8a041

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (μ : ℕ → ℕ) (p i : ℕ) (hi : p ≤ i) (m : ℕ) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) = ∏ j ∈ Finset.range m, xnT μ i j := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : ¬ i < p := by omega
  by_cases hij : i < j
  · have h2 : ¬ j < p := by omega
    simp only [xnT, xnAdd, if_pos hij, if_neg h1, if_neg h2, Nat.add_zero]
  · simp only [xnT, if_neg hij]
end Formalism.BranchingDeterminantCap
