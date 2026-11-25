-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.Dfun_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:16.55485+00:00
-- url     : https://prove2.me/submissions/8291be74-2cfe-4491-a14c-cdd8e038c4ea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_prod_map_pow_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_commute

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
theorem _root_.solution (e : Fin m × Fin n × Bool → ℕ) (k : Fin m × Fin n × Bool) :
    Dfun (fun i => e i + if i = k then 1 else 0) = Dfun e * ((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) :=
  prod_map_pow_single _ pderiv_commute e k _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))
end PositivityTheory.Rg.Sw.LC.CoreBb
