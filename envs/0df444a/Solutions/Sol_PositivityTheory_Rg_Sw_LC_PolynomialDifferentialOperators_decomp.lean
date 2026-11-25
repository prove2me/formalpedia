-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:15.401097+00:00
-- url     : https://prove2.me/submissions/ef790d95-b169-443d-b74f-10d90ff9ac6c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inl_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inl_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mapDomain_inr_inl

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (t : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl +
      (t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr = t := by
  ext j
  rcases j with j | j
  · simp [mapDomain_inl_inl, mapDomain_inr_inl, Finsupp.comapDomain_apply]
  · simp [mapDomain_inl_inr, mapDomain_inr_inr, Finsupp.comapDomain_apply]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
