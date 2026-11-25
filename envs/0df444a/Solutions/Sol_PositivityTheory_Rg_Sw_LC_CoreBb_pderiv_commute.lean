-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.pderiv_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:22.88147+00:00
-- url     : https://prove2.me/submissions/9c5a877f-75c6-48e1-b201-e1dd12551c7c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b

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
theorem _root_.solution (i j : Fin m × Fin n × Bool) :
    Commute ((pderiv (R := ℂ) i).toLinearMap : Module.End ℂ (PX m n)) (pderiv (R := ℂ) j).toLinearMap :=
  LinearMap.ext fun f => by simp [pderiv_comm' i j f]
end PositivityTheory.Rg.Sw.LC.CoreBb
