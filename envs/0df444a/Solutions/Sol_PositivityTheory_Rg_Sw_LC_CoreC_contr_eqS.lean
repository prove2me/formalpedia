-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.contr_eqS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:37.986999+00:00
-- url     : https://prove2.me/submissions/8daf06df-05b5-4852-a9ac-b709be199e00

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE

set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (c : ℝ) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) {p : PX m n} (hp : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, if Bal s then p.coeff s * piC c s else 0 := by
  unfold contr
  refine Finset.sum_subset hp fun s _ hs => ?_
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]
end PositivityTheory.Rg.Sw.LC.CoreC
