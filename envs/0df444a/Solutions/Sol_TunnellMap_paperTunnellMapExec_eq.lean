-- Prove2me | solution 1 for TunnellMap.paperTunnellMapExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:10:10.855416+00:00
-- url     : https://prove2.me/submissions/54c1a738-c290-4eb6-961e-8aa3f2ab463e

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_TunnellMap_oddMapExec_eq

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      paperTunnellMap hn hnpos hbalance p := by
  classical
  show _ = conditionalTunnellMap (paperOddEquiv hn hnpos hbalance)
    ((Equiv.sumCongr (evenRepParamEquiv n)
        ((Equiv.subtypeEquivRight (fun p : BRep n => Int.not_even_iff_odd)).trans
          (bOddSubtypeEquiv n)))
      ((Equiv.sumCompl (fun p : BRep n => Even p.1.z)).symm p))
  by_cases h : p.1.z % 2 = 0
  · have he : (fun p : BRep n => Even p.1.z) p := Int.even_iff.mpr h
    rw [Equiv.sumCompl_symm_apply_of_pos (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExec, dif_pos h]
    rfl
  · have he : ¬ (fun p : BRep n => Even p.1.z) p := fun hc => h (Int.even_iff.mp hc)
    rw [Equiv.sumCompl_symm_apply_of_neg (p := fun p : BRep n => Even p.1.z) he,
      paperTunnellMapExec, dif_neg h]
    show oddMapExec hnpos hsq fallback _ =
      paperOddEquiv hn hnpos hbalance ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
    exact oddMapExec_eq hn hnpos hsq (odd_card_eq_of_full_balance hbalance)
      fallback _
end TunnellMap
