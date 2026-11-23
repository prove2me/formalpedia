-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:22.901636+00:00
-- url     : https://prove2.me/submissions/82587bcf-ff16-4add-a1ec-2959593092aa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial s a =>
    simp only [pderiv_monomial]
    by_cases h : i = j
    · subst h; rfl
    · congr 1
      · rw [tsub_right_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]; ring
end PositivityTheory.Rg.Sw.LC.CoreBb
